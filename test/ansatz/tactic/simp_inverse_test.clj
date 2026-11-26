(ns ansatz.tactic.simp-inverse-test
  "Inverse simp rules (`simp [← h]`, `@[simp ←]`): Lean 4.36.0 SimpTheorems.lean:319-390
   `preprocess … inv`. Cases adapted from Lean's tests/elab/simpInv.lean and 4290.lean; every
   produced proof is re-checked by the kernel."
  (:require [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.instance-index :as instance-index]
            [ansatz.meta :as meta]
            [ansatz.tactic.simp.simp-theorems :as simp-theorems]))

(defn- require-env []
  (or @test-env/checked-bundled-init-env (throw (ex-info "bundled Init unavailable" {}))))

(def ^:private nat (e/const' (name/from-string "Nat") []))
(def ^:private prop (e/sort' lvl/zero))
(defn- c [s] (e/const' (name/from-string s) []))
(defn- eq-at [ty level x y] (e/app* (e/const' (name/from-string "Eq") [level]) ty x y))
(defn- eqn [x y] (eq-at nat (lvl/succ lvl/zero) x y))
(defn- iff [p q] (e/app* (c "Iff") p q))
(defn- and* [p q] (e/app* (c "And") p q))
(defn- ax [env n ty] (env/check-constant env (env/mk-axiom (name/from-string n) [] ty)))
(def ^:private nn (e/arrow nat (e/arrow nat nat)))
(def ^:private np (e/arrow nat (e/arrow nat prop)))
(defn- all2 [body] (e/forall' "x" nat (e/forall' "y" nat body :default) :default))

(defn- inv-env []
  (-> (require-env)
      (ax "SimpInv.f" nn) (ax "SimpInv.g" nn) (ax "SimpInv.x" nat)
      ;; simpInv.lean: axiom f_def (x y : Nat) : f x y = g x y; axiom f_ax (x : Nat) : f x x = x
      (ax "SimpInv.f_def" (all2 (eqn (e/app* (c "SimpInv.f") (e/bvar 1) (e/bvar 0))
                                     (e/app* (c "SimpInv.g") (e/bvar 1) (e/bvar 0)))))
      (ax "SimpInv.f_ax" (e/forall' "x" nat (eqn (e/app* (c "SimpInv.f") (e/bvar 0) (e/bvar 0)) (e/bvar 0))
                                    :default))
      ;; axiom p_def (x y : Nat) : p x y ↔ q x y; axiom p_ax (x : Nat) : p x x
      (ax "SimpInv.p" np) (ax "SimpInv.q" np)
      (ax "SimpInv.p_def" (all2 (iff (e/app* (c "SimpInv.p") (e/bvar 1) (e/bvar 0))
                                     (e/app* (c "SimpInv.q") (e/bvar 1) (e/bvar 0)))))
      (ax "SimpInv.p_ax" (e/forall' "x" nat (e/app* (c "SimpInv.p") (e/bvar 0) (e/bvar 0)) :default))
      ;; 4290.lean: abc : a = b ∧ a = c
      (ax "SimpInv.a" nat) (ax "SimpInv.b" nat) (ax "SimpInv.c" nat)
      (ax "SimpInv.abc" (and* (eqn (c "SimpInv.a") (c "SimpInv.b")) (eqn (c "SimpInv.a") (c "SimpInv.c"))))
      ;; rules that cannot be reversed
      (ax "SimpInv.ne" (e/arrow (eqn (c "SimpInv.a") (c "SimpInv.b")) (c "False")))
      (ax "SimpInv.not" (e/arrow (e/app* (c "SimpInv.p") (c "SimpInv.a") (c "SimpInv.b")) (c "False")))
      (ax "SimpInv.plain" (e/app* (c "SimpInv.p") (c "SimpInv.a") (c "SimpInv.b")))
      (ax "SimpInv.ne_app" (e/app* (e/const' (name/from-string "Ne") [(lvl/succ lvl/zero)]) nat
                                   (c "SimpInv.a") (c "SimpInv.b")))
      (ax "SimpInv.not_app" (e/app (c "Not") (e/app* (c "SimpInv.p") (c "SimpInv.a") (c "SimpInv.b"))))
      (ax "SimpInv.truth" (c "True"))
      (ax "SimpInv.mixed" (and* (eqn (c "SimpInv.a") (c "SimpInv.b")) (c "True")))
      (ax "SimpInv.P" prop)
      (ax "SimpInv.bare" (c "SimpInv.P"))
      ;; (∀ x, f x x = g x x) ∧ (a = b): a binder under And (Lean preprocess recurses with whnf)
      (ax "SimpInv.forall_and" (and* (e/forall' "x" nat (eqn (e/app* (c "SimpInv.f") (e/bvar 0) (e/bvar 0))
                                                             (e/app* (c "SimpInv.g") (e/bvar 0) (e/bvar 0))) :default)
                                     (eqn (c "SimpInv.a") (c "SimpInv.b"))))
      ;; offset: ∀ n, p n n ↔ q (succ n) n
      (ax "SimpInv.offset" (e/forall' "n" nat (iff (e/app* (c "SimpInv.p") (e/bvar 0) (e/bvar 0))
                                                   (e/app* (c "SimpInv.q") (e/app (c "Nat.succ") (e/bvar 0)) (e/bvar 0)))
                                      :default))
      ;; conditional: ∀ x, p x x → f x x = g x x
      (ax "SimpInv.cond" (e/forall' "x" nat (e/arrow (e/app* (c "SimpInv.p") (e/bvar 0) (e/bvar 0))
                                                     (eqn (e/app* (c "SimpInv.f") (e/bvar 1) (e/bvar 1))
                                                          (e/app* (c "SimpInv.g") (e/bvar 1) (e/bvar 1))))
                                    :default))
      (ax "SimpInv.p_xx" (e/app* (c "SimpInv.p") (c "SimpInv.x") (c "SimpInv.x")))
      ;; abbrev E a b := a = b; h : E a b
      (env/check-constant (env/mk-def (name/from-string "SimpInv.E") [] (e/arrow nat (e/arrow nat prop))
                                      (e/lam "a" nat (e/lam "b" nat (eqn (e/bvar 1) (e/bvar 0)) :default) :default)
                                      :hints :abbrev))
      (ax "SimpInv.e_ab" (e/app* (c "SimpInv.E") (c "SimpInv.a") (c "SimpInv.b")))
      ;; ∀ x, x = x: Lean's checkBadRewrite rejects it
      (ax "SimpInv.refl_all" (e/forall' "x" nat (eqn (e/bvar 0) (e/bvar 0)) :default))
      ;; ∀ x, (fun y => y) x = x: rejected too, the lhs reduces to x (reduceDT)
      (ax "SimpInv.beta_refl" (e/forall' "x" nat (eqn (e/app (e/lam "y" nat (e/bvar 0) :default) (e/bvar 0))
                                                      (e/bvar 0))
                                         :default))
      ;; ∀ f : Nat → Nat, (fun x => f x) = f: rejected, the lhs eta-reduces to f (reduceDT)
      (ax "SimpInv.eta_refl" (e/forall' "f" (e/arrow nat nat)
                                        (eq-at (e/arrow nat nat) (lvl/succ lvl/zero)
                                               (e/lam "x" nat (e/app (e/bvar 1) (e/bvar 0)) :default)
                                               (e/bvar 0))
                                        :default))
      ;; ∀ x, @Bool.rec (fun _ => Nat) x x false = x: accepted, simpGlobalConfig has iota := false
      (ax "SimpInv.rec_refl" (e/forall' "x" nat
                                        (eqn (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                                                     (e/lam "b" (c "Bool") nat :default)
                                                     (e/bvar 0) (e/bvar 0) (c "Bool.false"))
                                             (e/bvar 0))
                                        :default))
      ;; ∀ f : Nat → Nat, S f = R f (f a): the inverse pattern applies a rule parameter
      (ax "SimpInv.S" (e/arrow (e/arrow nat nat) nat))
      (ax "SimpInv.R" (e/arrow (e/arrow nat nat) (e/arrow nat nat)))
      (ax "SimpInv.kf" (e/arrow nat nat))
      (ax "SimpInv.sr" (e/forall' "f" (e/arrow nat nat)
                                  (eqn (e/app (c "SimpInv.S") (e/bvar 0))
                                       (e/app* (c "SimpInv.R") (e/bvar 0) (e/app (e/bvar 0) (c "SimpInv.a"))))
                                  :default))
      ;; ∀ x, (Prod.mk x x).1 = x as a raw projection: accepted, simpGlobalConfig has proj := .no
      (ax "SimpInv.proj_refl" (e/forall' "x" nat
                                         (eqn (e/proj (name/from-string "Prod") 0
                                                      (e/app* (e/const' (name/from-string "Prod.mk") [lvl/zero lvl/zero])
                                                              nat nat (e/bvar 0) (e/bvar 0)))
                                              (e/bvar 0))
                                         :default))
      ;; reducible idM whose body is `mdata (fun x => x)`; idM_eq : ∀ x, idM x = x
      (env/check-constant (env/mk-def (name/from-string "SimpInv.idM") [] (e/arrow nat nat)
                                      (e/mdata {} (e/lam "x" nat (e/bvar 0) :default))
                                      :hints :abbrev))
      (ax "SimpInv.idM_eq" (e/forall' "x" nat (eqn (e/app (c "SimpInv.idM") (e/bvar 0)) (e/bvar 0)) :default))
      ;; d0 x := x, d(i+1) x := di (di x) (reducible); dchain : ∀ x, d12 x = x, dchain17 for d17
      ((fn [env]
         (let [env (reduce (fn [env i]
                             (env/check-constant
                              env (env/mk-def (name/from-string (str "SimpInv.d" i)) [] (e/arrow nat nat)
                                              (e/lam "x" nat (if (zero? i)
                                                               (e/bvar 0)
                                                               (let [p (c (str "SimpInv.d" (dec i)))]
                                                                 (e/app p (e/app p (e/bvar 0)))))
                                                     :default)
                                              :hints :abbrev)))
                           env (range 18))]
           (-> env
               (ax "SimpInv.dchain" (e/forall' "x" nat (eqn (e/app (c "SimpInv.d12") (e/bvar 0)) (e/bvar 0)) :default))
               (ax "SimpInv.dchain17" (e/forall' "x" nat (eqn (e/app (c "SimpInv.d17") (e/bvar 0)) (e/bvar 0)) :default))))))
      ;; letchain : ∀ x, (let d0 := fun y => y; let d(i+1) := fun y => di (di y); … d17 x) = x
      ((fn [env]
         (let [nn (e/arrow nat nat)
               lets (fn lets [i]
                      (if (= i 18)
                        (e/app (e/bvar 0) (e/bvar 18))
                        (e/let' (str "d" i) nn
                                (if (zero? i)
                                  (e/lam "y" nat (e/bvar 0) :default)
                                  (e/lam "y" nat (e/app (e/bvar 1) (e/app (e/bvar 1) (e/bvar 0))) :default))
                                (lets (inc i)))))]
           (ax env "SimpInv.letchain" (e/forall' "x" nat (eqn (lets 0) (e/bvar 0)) :default)))))
      ;; reducible CM := mdata (fun n => C n): instance keys keep CM (no metadata-aware beta there)
      (ax "SimpInv.C" (e/arrow nat nat))
      (env/check-constant (env/mk-def (name/from-string "SimpInv.CM") [] (e/arrow nat nat)
                                      (e/mdata {} (e/lam "n" nat (e/app (c "SimpInv.C") (e/bvar 0)) :default))
                                      :hints :abbrev))
      ;; forward h : ∀ f, R f (f a) = W (R f (f a)) and j : a = b
      (ax "SimpInv.W" (e/arrow nat nat))
      (ax "SimpInv.rw" (e/forall' "f" (e/arrow nat nat)
                                  (let [rfa (e/app* (c "SimpInv.R") (e/bvar 0) (e/app (e/bvar 0) (c "SimpInv.a")))]
                                    (eqn rfa (e/app (c "SimpInv.W") rfa)))
                                  :default))
      (ax "SimpInv.ab" (eqn (c "SimpInv.a") (c "SimpInv.b")))))

(defn- simp-with [env entries expr]
  (let [st (tc/mk-tc-state env)
        index (simp/build-lemma-index st env (simp/make-simp-lemmas env entries))]
    (simp/simp-expr-result st env index expr)))

(defn- checks?
  "The rewrite's proof kernel-checks (env/verifies?: a missing proof is a failure)."
  [env lhs result]
  (let [st (tc/mk-tc-state env)
        ty (tc/infer-type st lhs)
        level (e/sort-level (#'tc/cached-whnf st (tc/infer-type st ty)))]
    (env/verifies? env (eq-at ty level lhs (:expr result)) (:proof? result))))

(defn- inv [n] {:name n :inv true})

(deftest inverse-eq-rule-simpInv-ex1
  (testing "with ← f_def and f_ax, g x x simplifies to x (Lean tests/elab/simpInv.lean ex1)"
    (let [env (inv-env)
          goal (e/app* (c "SimpInv.g") (c "SimpInv.x") (c "SimpInv.x"))
          r (simp-with env [(inv "SimpInv.f_def") "SimpInv.f_ax"] goal)]
      (is (= (c "SimpInv.x") (:expr r)))
      (is (checks? env goal r))
      (testing "the forward rule does not apply to g"
        (is (= goal (:expr (simp-with env ["SimpInv.f_def" "SimpInv.f_ax"] goal))))))))

(deftest inverse-iff-rule-simpInv-ex2
  (testing "with ← p_def and p_ax, q x x simplifies to True (Lean simpInv.lean ex2): Eq.symm (propext h)"
    (let [env (inv-env)
          goal (e/app* (c "SimpInv.q") (c "SimpInv.x") (c "SimpInv.x"))
          r (simp-with env [(inv "SimpInv.p_def") "SimpInv.p_ax"] goal)]
      (is (= (c "True") (:expr r)))
      (is (checks? env goal r)))))

(deftest inverse-of-a-conjunction-reverses-each-conjunct
  (testing "simp [← abc] with abc : a = b ∧ a = c rewrites b and c to a (Lean 4290.lean)"
    (let [env (inv-env)
          rules (simp/make-simp-lemmas env [(inv "SimpInv.abc")])]
      (is (= 2 (count rules)))
      (is (every? :inv rules))
      (doseq [x ["SimpInv.b" "SimpInv.c"]]
        (let [r (simp-with env [(inv "SimpInv.abc")] (c x))]
          (is (= (c "SimpInv.a") (:expr r)))
          (is (checks? env (c x) r)))))))

(deftest inverse-rule-keys-on-the-original-rhs
  (let [env (inv-env)
        [rule] (simp/make-simp-lemmas env [(inv "SimpInv.f_def")])]
    (is (= (name/from-string "SimpInv.g") (:head-name rule)))
    (is (:inv rule))
    (is (:post rule))
    (is (= ["SimpInv.f_def" true] (simp-theorems/rule-origin-key rule)))
    (is (= "← SimpInv.f_def" (simp-theorems/pp-origin (simp-theorems/rule-origin rule))))))

(deftest inverse-of-a-rewrite-to-false-or-true-is-rejected
  (let [env (inv-env)]
    (doseq [[n message] [["SimpInv.ne" #"Invalid `←` modifier"]
                         ["SimpInv.not" #"Invalid `←` modifier"]
                         ["SimpInv.plain" #"rewrites to `True`"]
                         ["SimpInv.ne_app" #"Invalid `←` modifier: Cannot be applied to simp theorems of the form `(a ≠ b|¬ P)`"]
                         ["SimpInv.not_app" #"form `¬ P`"]
                         ["SimpInv.truth" #"rewrites to `True`"]
                         ["SimpInv.mixed" #"rewrites to `True`"]
                         ["SimpInv.bare" #"rewrites to `True`"]]]
      (testing n
        (let [ex (try (simp/make-simp-lemmas env [(inv n)]) nil
                      (catch clojure.lang.ExceptionInfo ex ex))]
          (is (some? ex))
          (is (re-find message (ex-message ex)))
          (is (= :tactic-error (:kind (ex-data ex))))
          ;; the forward rule is fine (when it has one)
          (when-not (#{"SimpInv.truth" "SimpInv.bare"} n)
            (is (seq (simp/make-simp-lemmas env [n])))))))))

(deftest inverse-of-an-rfl-proof-stays-rfl
  (testing "an Eq.refl-proved theorem's inverse is rfl too (Ansatz detects rfl from the proof body;
            Lean transfers its [defeq] tag, SimpTheorems.lean:469)"
    (let [env (-> (inv-env)
                  (env/check-constant (env/mk-def (name/from-string "SimpInv.k") [] nat (e/lit-nat 7)))
                  (env/check-constant (env/mk-thm (name/from-string "SimpInv.k_eq") []
                                                  (eqn (c "SimpInv.k") (e/lit-nat 7))
                                                  (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                                          nat (e/lit-nat 7)))))
          [rule] (simp/make-simp-lemmas env [(inv "SimpInv.k_eq")])
          r (simp-with env [(inv "SimpInv.k_eq")] (e/lit-nat 7))]
      (is (:rfl rule))
      (is (= (c "SimpInv.k") (:expr r)))
      (is (nil? (:proof? r)))
      (testing "a proof-free step closes by reflexivity, which the kernel accepts"
        (is (env/verifies? env (eqn (e/lit-nat 7) (:expr r))
                           (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)])
                                   nat (e/lit-nat 7))))))))

(deftest inverse-proof-term-rule
  (testing "a proof term reversed under its binders (Lean mkSimpTheoremFromExpr … inv)"
    (let [env (inv-env)
          st (tc/mk-tc-state env)
          ;; a partially applied theorem: ∀ y, f x y = g x y
          term (e/app (c "SimpInv.f_def") (c "SimpInv.x"))
          rules (#'simp/extract-simp-lemma-term env (tc/infer-type st term) 1000 term {:inv true})
          index (simp/build-lemma-index st env (concat rules (simp/make-simp-lemmas env ["SimpInv.f_ax"])))
          goal (e/app* (c "SimpInv.g") (c "SimpInv.x") (c "SimpInv.x"))
          r (simp/simp-expr-result st env index goal)]
      (is (= (c "SimpInv.x") (:expr r)))
      (is (checks? env goal r)))))

(deftest inverse-preprocessing-reduces-and-opens-binders-under-and
  (let [env (inv-env)]
    (testing "an abbreviation unfolds to its equation (Lean whnfR, SimpTheorems.lean:328)"
      (let [r (simp-with env [(inv "SimpInv.e_ab")] (c "SimpInv.b"))]
        (is (= (c "SimpInv.a") (:expr r)))
        (is (checks? env (c "SimpInv.b") r)))
      (testing "also without any reducibility metadata (the abbrev hint decides)"
        (let [bare (env/with-extension env :reducibility-status {})
              r (simp-with bare [(inv "SimpInv.e_ab")] (c "SimpInv.b"))]
          (is (= (c "SimpInv.a") (:expr r)))
          (is (checks? bare (c "SimpInv.b") r)))))
    (testing "a quantified conjunct keeps its binder: λ x. Eq.symm (h.1 x)"
      (let [rules (simp/make-simp-lemmas env [(inv "SimpInv.forall_and")])
            goal (e/app* (c "SimpInv.g") (c "SimpInv.x") (c "SimpInv.x"))
            r (simp-with env [(inv "SimpInv.forall_and")] goal)]
        (is (= 2 (count rules)))
        (is (= (e/app* (c "SimpInv.f") (c "SimpInv.x") (c "SimpInv.x")) (:expr r)))
        (is (checks? env goal r))
        (let [r (simp-with env [(inv "SimpInv.forall_and")] (c "SimpInv.b"))]
          (is (= (c "SimpInv.a") (:expr r)))
          (is (checks? env (c "SimpInv.b") r)))))))

(deftest inverse-iff-rule-matches-like-an-equation
  (testing "an inverse Iff is the Eq `r = l` (Lean's aux lemma), so offset matching applies"
    (let [env (inv-env)
          three (e/lit-nat 3)
          goal (e/app* (c "SimpInv.q") three (e/lit-nat 2))
          r (simp-with env [(inv "SimpInv.offset")] goal)]
      (is (= (c "SimpInv.p") (e/get-app-fn (:expr r))))
      (is (checks? env goal r)))))

(deftest conditional-inverse-needs-its-premise
  (let [env (inv-env)
        goal (e/app* (c "SimpInv.g") (c "SimpInv.x") (c "SimpInv.x"))]
    (testing "without the premise the rule does not fire"
      (is (= goal (:expr (simp-with env [(inv "SimpInv.cond")] goal)))))
    (testing "with it (discharged by p_xx) it does"
      (let [r (simp-with env [(inv "SimpInv.cond") "SimpInv.p_xx"] goal)]
        (is (= (e/app* (c "SimpInv.f") (c "SimpInv.x") (c "SimpInv.x")) (:expr r)))
        (is (checks? env goal r))))))

(deftest inverse-rule-origin-phase-and-priority
  (let [env (inv-env)
        [pre] (simp/make-simp-lemmas env [{:name "SimpInv.f_def" :inv true :post false}])
        [explicit] (simp/make-simp-lemmas env [{:name "SimpInv.f_def" :inv true :priority 1234}])
        [inherited] (simp/make-simp-lemmas (env/update-extension env :simp-priorities {} assoc "SimpInv.f_def" 77)
                                           [{:name "SimpInv.f_def" :inv true}])]
    (is (false? (:post pre)))
    (is (true? (:inv pre)))
    (is (= 1234 (:priority explicit)))
    (is (= 77 (:priority inherited)))))

(deftest polymorphic-inverse-at-two-universes
  (testing "List.length_append reversed: as.length + bs.length ↦ (as ++ bs).length at Type and Type 1"
    (let [env (require-env)
          [rule :as rules] (simp/make-simp-lemmas env [{:name "List.length_append" :inv true}])
          [u-param] (:level-params rule)]
      (is (= 1 (count rules)))
      (doseq [[alpha u] [[nat lvl/zero] [(e/sort' (lvl/succ lvl/zero)) (lvl/succ lvl/zero)]]]
        (let [list-ty (e/app (e/const' (name/from-string "List") [u]) alpha)
              st (tc/attach-lctx (tc/mk-tc-state env) {991301 {:tag :local :id 991301 :name "as" :type list-ty}
                                                       991302 {:tag :local :id 991302 :name "bs" :type list-ty}})
              ;; the rule's own lhs at u, α, as, bs (bvar 0 is the innermost binder, bs)
              goal (-> (e/instantiate-level-params (:lhs-pattern rule) {u-param u})
                       (e/instantiate1 (e/fvar 991302)) (e/instantiate1 (e/fvar 991301)) (e/instantiate1 alpha))
              index (simp/build-lemma-index st env rules)
              r (simp/simp-expr-result st env index goal)]
          (is (not= goal (:expr r)))
          (is (some? (:proof? r)))
          (is (= "List.length" (str (e/const-name (e/get-app-fn (:expr r))))))
          (testing "the proof, closed over as and bs, kernel-checks against ∀ as bs, goal = result"
            (let [close (fn [mk x]
                          (mk "as" list-ty (mk "bs" list-ty (e/abstract-many x [991301 991302]) :default) :default))]
              (is (env/verifies? env (close e/forall' (eqn goal (:expr r))) (close e/lam (:proof? r)))))))))))

(deftest inverse-of-a-non-theorem-or-a-bad-rewrite-is-rejected
  (let [env (inv-env)]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Expected a proposition"
                          (simp/make-simp-lemmas env [(inv "Nat.zero")])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Equation is equivalent to"
                          (simp/make-simp-lemmas env [(inv "SimpInv.refl_all")])))
    (testing "the lhs is reduced first (Lean checkBadRewrite reduceDT): a beta redex of x is x"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Equation is equivalent to"
                            (simp/make-simp-lemmas env [(inv "SimpInv.beta_refl")]))))
    (testing "strict eta: (fun x => f x) is f"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Equation is equivalent to"
                            (simp/make-simp-lemmas env [(inv "SimpInv.eta_refl")]))))))

(deftest inverse-bad-rewrite-check-does-not-reduce-recursors
  (testing "simpGlobalConfig has iota := false: a raw recursor application on false stays"
    (let [rules (simp/make-simp-lemmas (inv-env) [(inv "SimpInv.rec_refl")])]
      (is (= 1 (count rules)))
      (is (every? :inv rules))))
  (testing "proj := .no: a raw projection of a constructor stays"
    (let [rules (simp/make-simp-lemmas (inv-env) [(inv "SimpInv.proj_refl")])]
      (is (= 1 (count rules)))
      (is (every? :inv rules)))))

(deftest inverse-bad-rewrite-check-unfolds-through-metadata
  (testing "delta-beta looks through metadata (Lean betaRev): idM x is x"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Equation is equivalent to"
                          (simp/make-simp-lemmas (inv-env) [(inv "SimpInv.idM_eq")])))))

(deftest inverse-bad-rewrite-check-has-a-step-limit
  ;; test/lean-parity/simp/a_bad_rewrite_chain.lean: Lean v4.36.0 rejects d12 x = x
  (testing "d12 x needs 2^13 unfoldings and reduces to x, as in Lean"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Equation is equivalent to"
                          (simp/make-simp-lemmas (inv-env) [(inv "SimpInv.dchain")]))))
  (testing "d17 x needs 2^18: the reduction stops at its limit (Lean is bounded only by heartbeats)"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"maxRecDepth"
                          (simp/make-simp-lemmas (inv-env) [(inv "SimpInv.dchain17")]))))
  (testing "the same chain as let-bound lambdas: zeta and beta steps count too"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"maxRecDepth"
                          (simp/make-simp-lemmas (inv-env) [(inv "SimpInv.letchain")])))))

(deftest metadata-aware-beta-is-scoped-to-the-bad-rewrite-guard
  ;; the instance index keys CM 0 under CM, as persisted version-2 registries do
  (let [env (inv-env)
        st (tc/mk-tc-state env)
        q (e/app (c "SimpInv.CM") (e/lit-nat 0))]
    (is (= (c "SimpInv.CM") (e/get-app-fn (instance-index/reduce-dt meta/empty-context st q true))))))

(deftest inverse-of-a-local-reflexive-proof-is-accepted
  (testing "the x = x check is for global declarations only (Lean preprocess isGlobal := false)"
    (let [env (inv-env)
          st (tc/attach-lctx (tc/mk-tc-state env) {991401 {:tag :local :id 991401 :name "x" :type nat}
                                                   991402 {:tag :local :id 991402 :name "h"
                                                           :type (eqn (e/fvar 991401) (e/fvar 991401))}})
          rules (#'simp/extract-simp-lemma-term env (eqn (e/fvar 991401) (e/fvar 991401)) 1000 (e/fvar 991402)
                                                {:inv true :st st})]
      (is (= 1 (count rules)))
      (is (every? :inv rules)))
    (testing "a non-proposition term is rejected as such (checkTypeIsProp)"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Expected a proposition"
                            (#'simp/extract-simp-lemma-term (inv-env) nat 1000 (e/lit-nat 1) {:inv true}))))))

(deftest inverse-rule-with-an-applied-parameter-is-indexed
  (testing "← sr rewrites R kf (kf a) to S kf: the parameter-headed f a is a wildcard key (Lean mvar app)"
    (let [env (inv-env)
          goal (e/app* (c "SimpInv.R") (c "SimpInv.kf") (e/app (c "SimpInv.kf") (c "SimpInv.a")))
          r (simp-with env [(inv "SimpInv.sr")] goal)]
      (is (= (e/app (c "SimpInv.S") (c "SimpInv.kf")) (:expr r)))
      (is (checks? env goal r)))))

(deftest forward-rule-with-an-applied-parameter-waits-for-its-arguments
  (testing "h : R f (f a) = W (R f (f a)) keeps its forward keys: j : a = b rewrites first"
    (let [env (inv-env)
          goal (e/app* (c "SimpInv.R") (c "SimpInv.kf") (e/app (c "SimpInv.kf") (c "SimpInv.a")))
          r (simp-with env ["SimpInv.rw" "SimpInv.ab"] goal)]
      (is (= (e/app* (c "SimpInv.R") (c "SimpInv.kf") (e/app (c "SimpInv.kf") (c "SimpInv.b"))) (:expr r)))
      (is (checks? env goal r)))))
