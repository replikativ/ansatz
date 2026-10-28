(ns ansatz.tactic.rcases-test
  (:require [clojure.test :refer [deftest is use-fixtures testing]]
            [ansatz.core :as a]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.simp :as simp]
            [clojure.walk :as walk]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

(use-fixtures :once
  (fn [f]
    (a/load-init!)
    ;; The bundled small Init fixture omits Sigma and Sum. Declare their
    ;; constructor shapes here, including Sigma's dependent second field.
    (binding [a/*verbose* false]
      (a/inductive TestSigma [A Type B (=> A Type)]
                   (mk [fst A] [snd (B fst)]))
      (a/inductive TestSum [A Type B Type]
                   (inl [val A]) (inr [val B]))
      (binding [*ns* (the-ns 'ansatz.tactic.rcases-test)]
        (a/structure FrameState [] (x Nat))
        (a/structure FrameOutcome [] (state FrameState) (accepted Bool))
        (a/defn frame-step [n :- Nat, s :- FrameState] FrameOutcome
          (if (Nat.beq n 0) (FrameOutcome.mk s true) (FrameOutcome.mk s false)))
        (a/defn probe-case-f [n :- Nat] (Option Nat)
          (match n
            [0 (Option.some Nat 0)]
            [_ (Option.none Nat)])))
      (f))))

(defn- proves [params target tactics]
  ;; prove-theorem constructs a declaration and runs check-constant.
  (a/prove-theorem (gensym "rcases_test_") params target tactics)
  true)

(deftest tuple-patterns
  (is (proves '[p :- (Prod Nat Nat)] '(= (+ (Prod.fst Nat Nat p) 0) (Prod.fst Nat Nat p))
              '[(rcases p [a _]) (exact (Nat.add_zero a))]))
  (is (proves '[h :- (And True (And True True))] 'True
              '[(rcases h [a b c]) (exact c)]))
  (is (proves '[h :- (And True (And True True))] 'True
              '[(rcases h [_ [b c]]) (exact b)])))

(deftest existential-and-sigma-patterns
  (is (proves '[h :- (Exists Nat (fn [x :- Nat] (= x 0)))]
              '(Exists Nat (fn [x :- Nat] (= x 0)))
              '[(rcases h [x hx]) (exact (Exists.intro Nat (fn [x :- Nat] (= x 0)) x hx))]))
  (is (proves '[A :- Type, B :- (=> A Type), p :- (TestSigma A B)]
              '(Exists A (fn [x :- A] (Exists (B x) (fn [y :- (B x)] (= y y)))))
              '[(rcases p [a b])
                (exact (Exists.intro A (fn [x :- A] (Exists (B x) (fn [y :- (B x)] (= y y)))) a
                                     (Exists.intro (B a) (fn [y :- (B a)] (= y y)) b (Eq.refl (B a) b))))])))

(deftest alternative-patterns
  (is (proves '[h :- True] 'True '[(rcases h (or a)) (exact a)]))
  (is (proves '[h :- (Or (And True True) True)] 'True
              '[(rcases h (or [a b] c)) (exact b) (exact c)]))
  (is (proves '[h :- (Or True (Or True True))] 'True
              '[(rcases h (or a b c)) (exact a) (exact b) (exact c)]))
  (is (proves '[h :- (TestSum Nat Nat)] '(Exists Nat (fn [x :- Nat] (= x x)))
              '[(rcases h (or a b))
                (exact (Exists.intro Nat (fn [x :- Nat] (= x x)) a (Eq.refl Nat a)))
                (exact (Exists.intro Nat (fn [x :- Nat] (= x x)) b (Eq.refl Nat b)))]))
  (is (proves '[h :- (And (Or True True) True)] 'True
              '[(rcases h [(or a b) c]) (exact c) (exact c)])))

(deftest rfl-patterns
  (is (proves '[x :- Nat, y :- Nat, h :- (= x y)] '(= x x)
              '[(rcases h rfl) (exact (Eq.refl Nat x))]))
  (is (proves '[x :- Nat, h :- (= x 0)] '(= x 0)
              '[(rcases h rfl) (rfl)]))
  (is (proves '[h :- (Exists Nat (fn [x :- Nat] (= x 0)))] 'True
              '[(rcases h [x rfl]) (trivial)])))

(deftest obtain-patterns
  (is (proves '[p :- (Prod Nat Nat)] '(= (Prod.fst Nat Nat p) (Prod.fst Nat Nat p))
              '[(obtain [a b] := p) (exact (Eq.refl Nat a))]))
  (is (proves '[] 'True
              '[(obtain [a b] :- (And True True) := (And.intro True True True.intro True.intro))
                (exact a)]))
  (is (proves '[] 'True
              '[(obtain [a b] := (Prod.mk Nat Nat 1 2)) (trivial)])))

(deftest general-cases-equations
  (is (proves '[n :- Nat] '(= n n)
              '[(cases h n) (rfl) (rfl)]))
  (is (proves '[p :- (Prod Nat Nat)] 'True
              '[(cases h p) (trivial)]))
  (is (proves '[b :- Bool] '(= b b)
              '[(cases h b) (rfl) (rfl)])))

(deftest trivial-alternatives
  (doseq [[params target] [['[] 'True]
                           ['[] '(And True (And (= Nat 0 0) True))]
                           ['[p :- Prop, h :- p] 'p]
                           ['[n :- Nat] '(= n n)]
                           ['[] '(= (+ 1 1) 2)]
                           ['[] '(<= Nat 2 3)]
                           ['[h :- False] '(= Nat 0 1)]]]
    (testing (str params " |- " target)
      (is (proves params target '[(trivial)]))))
  (is (thrown? clojure.lang.ExceptionInfo
               (proves '[] 'False '[(trivial)]))))

(deftest anonymous-and-failure-patterns
  (is (proves '[h :- True] 'True '[(rcases h _) (assumption)]))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"invalid pattern"
                        (proves '[h :- True] 'True '[(rcases h :invalid)])))
  (is (thrown-with-msg? NullPointerException #"injected defect"
                        (with-redefs [basic/apply-tac (fn [& _] (throw (NullPointerException. "injected defect")))]
                          (proves '[] 'True '[(trivial)])))))

(deftest regression-obtain-local-scrutinee
  (doseq [tac '[(obtain [a b] := p) (obtain [a b] :- (Prod Nat Nat) := p)]]
    (is (proves '[p :- (Prod Nat Nat)]
                '(= (Prod.fst Nat Nat p) (Prod.fst Nat Nat p))
                [tac '(exact (Eq.refl Nat a))]))))

(deftest obtain-rejects-surplus-constructor-patterns
  (is (proves '[x :- Bool, h :- (= Bool x true)] '(= Bool x x)
              '[(try (obtain [a b] := h)) (rfl)]))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"more fields"
                        (proves '[x :- Bool, h :- (= Bool x true)] '(= Bool x x)
                                '[(obtain [a b] := h) (rfl)]))))

(deftest cases-rejects-stuck-function-as-constructor
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"cannot solve equality"
                        (proves '[n :- Nat, c :- Nat,
                                  h :- (= (Option Nat) (probe-case-f n)
                                          (Option.some Nat c))]
                                'True
                                '[(cases h) (all_goals (trivial))]))))

(deftest regression-rfl-normalizes-sides
  (is (proves '[x :- Nat, y :- Nat, h :- (= x ((fn [z :- Nat] z) y))]
              '(= x x)
              '[(rcases h rfl) (exact (Eq.refl Nat x))]))
  (is (proves '[x :- Nat, h :- (= ((fn [z :- Nat] z) x) 0)] '(= x 0)
              '[(rcases h rfl) (exact (Eq.refl Nat 0))])))

(deftest regression-rfl-proof-dependents
  ;; Use both the surviving variable and the reverted/reintroduced proof local.
  (is (proves '[x :- Nat, y :- Nat, h :- (= x y), h2 :- (= h h)]
              '(= x x)
              '[(rcases h rfl) (have keep (= (Eq.refl Nat x) (Eq.refl Nat x)) := h2)
                (exact (Eq.refl Nat x))]))
  ;; Forward substitution uses the auxiliary symmetric proof in Eq.rec's motive.
  (is (proves '[x :- Nat, h :- (= x 0), h2 :- (= h h), h3 :- (= h2 h2)]
              '(= x 0)
              '[(rcases h rfl)
                (have keep (= (Eq.refl Nat 0) (Eq.refl Nat 0)) := h2)
                (have keep2 (= h2 h2) := h3) (exact (Eq.refl Nat 0))])))

(deftest regression-cases-equations
  ;; The branch function can only be applied using the named equation.
  (is (proves '[b :- Bool, P :- Prop,
                hf :- (=> (= b false) P), ht :- (=> (= b true) P)] 'P
              '[(cases h b) (exact (hf h)) (exact (ht h))]))
  ;; The compound discriminant is absent from the target, and occurs only
  ;; in the hypotheses. Generalize must still introduce its equation.
  (is (proves '[b :- Bool, P :- Prop,
                hf :- (=> (= (Bool.not b) false) P),
                ht :- (=> (= (Bool.not b) true) P)] 'P
              '[(cases h (Bool.not b)) (exact (hf h)) (exact (ht h))])))

(deftest regression-trivial-does-not-use-simp
  ;; An ambient simp implementation must never be invoked by built-in trivial.
  (with-redefs [simp/simp (fn [& _] (throw (AssertionError. "trivial invoked simp")))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Tactic error: trivial failed"
                          (proves '[] 'False '[(trivial)])))))

(defn- defines [params target tactics]
  ;; Type-valued goals are definitions in Lean, not theorem declarations.
  (let [[ty term] (a/prove-law params target tactics)]
    (env/check-constant (a/env) (env/mk-def (name/from-string (str (gensym "subst_def_"))) [] ty term)))
  true)

(deftest rereview-subst-motive-universe
  (let [params (walk/postwalk-replace
                {'HIGH (symbol "Type.{1}")}
                '[x :- Nat, y :- Nat, h :- (= x y), P :- (=> Nat HIGH), p :- (P y)])]
    ;; Regression: reverting p raises a Nat-valued motive's sort.
    (is (defines params 'Nat '[(rcases h rfl) (exact 0)]))
    ;; Require the substituted p : P x, not just a closed constant proof.
    (is (defines params '(P x) '[(rcases h rfl) (exact p)]))
    ;; Eq.rec also infers its universe from the completed dependent motive.
    (is (defines (into params '[h2 :- (= h h)]) '(P x)
          '[(rcases h rfl)
            (have keep (= (Eq.refl Nat x) (Eq.refl Nat x)) := h2) (exact p)]))))

(deftest rereview-rfl-heq-conversion
  (is (proves '[x :- Nat, y :- Nat, h :- (HEq Nat x Nat y)] '(= x x)
              '[(rcases h rfl) (exact (Eq.refl Nat x))]))
  ;; Here substitution is required to inhabit the original target at all.
  (is (proves '[x :- Nat, y :- Nat, h :- (HEq Nat x Nat y),
                P :- (=> Nat Prop), p :- (P y)] '(P x)
              '[(rcases h rfl) (exact p)]))
  (is (proves '[x :- Nat, y :- Nat,
                h :- (HEq Nat x ((fn [T :- Type] T) Nat) y),
                P :- (=> Nat Prop), p :- (P y), h2 :- (= h h)] '(P x)
              '[(rcases h rfl) (have keep (= h2 h2) := (Eq.refl _ h2)) (exact p)])))

(deftest cases-equations-under-projections
  (is (proves '[n :- Nat, s :- FrameState]
              '(= (:state (frame-step n s)) s)
              '[(and_then (cases h (Nat.beq n 0)) (simp [frame-step h]))]))
  (is (proves '[n :- Nat, s :- FrameState]
              '(= (:x (:state (frame-step n s))) (:x s))
              '[(and_then (cases h (Nat.beq n 0)) (simp [frame-step h]))]))
  (is (proves '[s :- FrameOutcome]
              '(= (:accepted s) (:accepted s))
              '[(cases h (:accepted s)) (exact (Eq.refl Bool false)) (exact (Eq.refl Bool true))]))
  (is (proves '[s :- FrameOutcome]
              '(= (:x (:state s)) (:x (:state s)))
              '[(generalize x h (:x (:state s))) (intro x) (intro h) (exact (Eq.refl Nat x))])))

(deftest generalization-visits-projection-children
  (is (proves '[s :- FrameState, b :- Bool]
              '(= (:accepted (FrameOutcome.mk s (Bool.not b))) (Bool.not b))
              '[(cases h (Bool.not b)) (exact (Eq.refl Bool false)) (exact (Eq.refl Bool true))]))
  (is (proves '[n :- Nat, b :- Bool]
              '(= (:x (:state (FrameOutcome.mk (FrameState.mk (Nat.succ n)) b))) (Nat.succ n))
              '[(generalize x h (Nat.succ n)) (intro x) (intro h) (exact (Eq.refl Nat x))])))

(deftest generalization-rejects-ill-typed-target
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"generalize: result is not type correct"
                        (proves '[n :- Nat, x :- (Fin n)] '(= x x)
                                '[(generalize k h n)]))))
