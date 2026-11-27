(ns ansatz.tactic.simp-arg-modifiers-test
  "Lean simp argument modifiers `↓ x`, `← x`, `-x` (Init/Tactics.lean:694-705,
   Elab/Tactic/Simp.lean:322-470). Lean pairs: tests/elab/simpInv.lean, 4290.lean,
   eraseSimp.lean, simp_leftarrow_simproc.lean."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.tactic.simp :as simp]))

(use-fixtures :once
  (fn [t]
    (a/load-init!)
    (binding [a/*verbose* false *ns* (the-ns 'ansatz.tactic.simp-arg-modifiers-test)]
      (t))))

(defn- proves? [form]
  (let [before (a/env)]
    (try (eval form) true
         (finally (reset! a/ansatz-env before)))))

(defn- fails-with? [re form]
  (let [before (a/env)]
    (try (eval form) false
         (catch clojure.lang.ExceptionInfo ex (boolean (re-find re (ex-message ex))))
         (finally (reset! a/ansatz-env before)))))

(deftest inverse-hypotheses-simpInv
  (testing "simpInv.lean ex1 over local hypotheses: simp [← f_def, f_ax]"
    (is (proves? '(a/theorem simp-inv-ex1
                             [f :- (=> Nat Nat Nat), g :- (=> Nat Nat Nat), x :- Nat,
                              f_def :- (forall [y :- Nat, z :- Nat] (= Nat (f y z) (g y z))),
                              f_ax :- (forall [y :- Nat] (= Nat (f y y) y))]
                             (= Nat (g x x) x)
                             (simp [← f_def f_ax]))))
    (testing "ASCII `<-` is the same modifier"
      (is (proves? '(a/theorem simp-inv-ex1-ascii
                               [f :- (=> Nat Nat Nat), g :- (=> Nat Nat Nat), x :- Nat,
                                f_def :- (forall [y :- Nat, z :- Nat] (= Nat (f y z) (g y z))),
                                f_ax :- (forall [y :- Nat] (= Nat (f y y) y))]
                               (= Nat (g x x) x)
                               (simp [<- f_def f_ax]))))))
  (testing "simpInv.lean ex2 (Iff): simp [← p_def, p_ax]"
    (is (proves? '(a/theorem simp-inv-ex2
                             [p :- (=> Nat Nat Prop), q :- (=> Nat Nat Prop), x :- Nat,
                              p_def :- (forall [y :- Nat, z :- Nat] (Iff (p y z) (q y z))),
                              p_ax :- (forall [y :- Nat] (p y y))]
                             (q x x)
                             (simp [← p_def]) (exact (p_ax x))))))
  (testing "4290.lean abc: each conjunct reversed"
    (is (proves? '(a/theorem simp-inv-abc
                             [a :- Nat, b :- Nat, c :- Nat, abc :- (And (= Nat a b) (= Nat a c))]
                             (= Nat a c)
                             (simp [← abc]))))))

(deftest pre-modifier
  (testing "simp [↓ h] rewrites with h"
    (is (proves? '(a/theorem simp-pre-arg
                             [F :- (=> Nat Nat), G :- (=> Nat Nat), x :- Nat,
                              h :- (forall [y :- Nat] (= Nat (F (G y)) y))]
                             (= Nat (F (G x)) x)
                             (simp [↓ h]))))))

(defn- with-axioms
  "Run `f` with the global env extended by `env-fn` (restored afterwards)."
  [env-fn f]
  (let [before (a/env)]
    (try (reset! a/ansatz-env (env-fn before)) (f)
         (finally (reset! a/ansatz-env before)))))

(def ^:private nat (ansatz.kernel.expr/const' (ansatz.kernel.name/from-string "Nat") []))
(defn- k [s] (ansatz.kernel.expr/const' (ansatz.kernel.name/from-string s) []))
(defn- eqn* [x y] (ansatz.kernel.expr/app* (ansatz.kernel.expr/const' (ansatz.kernel.name/from-string "Eq")
                                                                      [(ansatz.kernel.level/succ ansatz.kernel.level/zero)])
                                           nat x y))
(defn- ax* [env n ty] (ansatz.kernel.env/check-constant env (ansatz.kernel.env/mk-axiom (ansatz.kernel.name/from-string n) [] ty)))

(defn- argT-env
  "Opaque a b, P, t : a = b; D with a registered @[simp] equation D.eq_1 : D = a (toUnfoldThms)."
  [env]
  (-> env
      (ax* "ArgT.a" nat) (ax* "ArgT.b" nat)
      (ax* "ArgT.P" (ansatz.kernel.expr/arrow nat (ansatz.kernel.expr/sort' ansatz.kernel.level/zero)))
      (ax* "ArgT.t" (eqn* (k "ArgT.a") (k "ArgT.b")))
      ;; opaque here, so only the registered equation can relate D and a
      (ax* "ArgT.D" nat)
      (ax* "ArgT.D.eq_1" (eqn* (k "ArgT.D") (k "ArgT.a")))
      (ansatz.kernel.env/update-extension :simp-lemmas #{} conj "ArgT.D.eq_1")
      (ansatz.kernel.env/update-extension :simp-unfold-thms {} assoc "ArgT.D" ["ArgT.D.eq_1"])))

(deftest erase-modifier
  (testing "without `*`, `-h` names a global declaration (Elab/Tactic/Simp.lean:430)"
    (is (fails-with? #"Unknown constant: h"
                     '(a/theorem simp-erase-hyp [f :- (=> Nat Nat), a :- Nat, h :- (= Nat (f a) a)]
                                 (= Nat (f (f a)) a) (simp [h -h]))))
    (is (fails-with? #"Unknown constant: h"
                     '(a/theorem simp-erase-hyp-spaced [f :- (=> Nat Nat), a :- Nat, h :- (= Nat (f a) a)]
                                 (= Nat (f (f a)) a) (simp [h - h])))))
  (testing "after `*`, `-h` erases the hypothesis `*` added; an explicit `h` stays"
    (is (proves? '(a/theorem simp-star [f :- (=> Nat Nat), a :- Nat, h :- (= Nat (f a) a)]
                             (= Nat (f (f a)) a) (simp [*]))))
    (is (fails-with? #"Proof incomplete|made no progress"
                     '(a/theorem simp-erase-star [f :- (=> Nat Nat), a :- Nat, h :- (= Nat (f a) a)]
                                 (= Nat (f (f a)) a) (simp [* -h]))))
    (is (proves? '(a/theorem simp-erase-star-explicit [f :- (=> Nat Nat), a :- Nat, h :- (= Nat (f a) a)]
                             (= Nat (f (f a)) a) (simp [* -h h])))))
  (testing "simp_all erases locals (eraseLocal) and neither simplifies nor uses them (SimpAll.lean:39-53)"
    (is (proves? '(a/theorem simp-all-uses-h [P :- Prop, h :- (And True False)] P (simp_all))))
    (is (fails-with? #"Proof incomplete|made no progress|no progress"
                     '(a/theorem simp-all-erases-h [P :- Prop, h :- (And True False)] P (simp_all [-h]))))))

(deftest simp-all-uses-the-same-arguments-for-hypotheses-and-target
  ;; `t` itself is a hypothesis simp_all rewrites with (f ↦ g), so it is erased; the explicit
  ;; term `(t x)` has no `.fvar` origin (Lean `.stx`) and stays.
  (testing "simp_all only [-t, ← (t x)] rewrites the hypothesis with the explicit term"
    (is (proves? '(a/theorem simp-all-only-term
                             [f :- (=> Nat Nat), g :- (=> Nat Nat), P :- (=> Nat Prop), x :- Nat,
                              t :- (forall [y :- Nat] (= Nat (f y) (g y))), h :- (P (g x))]
                             (P (f x))
                             ;; h becomes h' : P (f x); an fvar-headed hypothesis is no simp rule
                             ;; here yet (a separate gap), so close with it explicitly
                             (simp_all only [-t ← (t x)]) (exact h')))))
  (testing "without the explicit term nothing relates g x back to f x"
    (is (fails-with? #"Proof incomplete|made no progress|no progress"
                     '(a/theorem simp-all-only-no-term
                                 [f :- (=> Nat Nat), g :- (=> Nat Nat), P :- (=> Nat Prop), x :- Nat,
                                  t :- (forall [y :- Nat] (= Nat (f y) (g y))), h :- (P (g x))]
                                 (P (f x))
                                 (simp_all only [-t]))))))

(deftest converse-erasure-is-symmetric-and-sticky
  ;; Lean addSimpTheorem/eraseFwdIfBwd (SimpTheorems.lean:634-652) and issue5828.lean
  (with-axioms argT-env
    (fn []
      (let [env (a/env)
            ctx {}]
        (testing "[← t, t]: the final t leaves only the forward rule"
          (let [r (simp/elab-simp-args env [{:name "ArgT.t" :inv true} 'ArgT.t] ctx)]
            (is (contains? (:erased r) ["ArgT.t" true]))
            (is (not (contains? (:erased r) ["ArgT.t" false])))))
        (testing "[t, ← t, -t]: -t erases the live ←t"
          (let [r (simp/elab-simp-args env ['ArgT.t {:name "ArgT.t" :inv true} {:erase "ArgT.t"}] ctx)]
            (is (contains? (:erased r) ["ArgT.t" true]))
            (is (contains? (:erased r) ["ArgT.t" false]))))
        (testing "a re-added origin is un-erased"
          (let [r (simp/elab-simp-args env [{:erase "ArgT.t"} 'ArgT.t] {:inherited? #{["ArgT.t" false]}})]
            (is (not (contains? (:erased r) ["ArgT.t" false])))))
        (testing "normal forms, both orders: P b ↦ P a with ← t, P a ↦ P b with t"
          (is (proves? '(a/theorem conv-inv [h :- (ArgT.P ArgT.a)] (ArgT.P ArgT.b) (simp only [ArgT.t ← ArgT.t]) (exact h))))
          (is (proves? '(a/theorem conv-fwd [h :- (ArgT.P ArgT.b)] (ArgT.P ArgT.a) (simp only [← ArgT.t ArgT.t]) (exact h)))))))))

(deftest erasing-a-definition-erases-its-registered-equations
  ;; Lean eraseCore cascades through toUnfoldThms (SimpTheorems.lean:612-622)
  (with-axioms argT-env
    (fn []
      (is (proves? '(a/theorem d-eq [h :- (ArgT.P ArgT.a)] (ArgT.P ArgT.D) (simp) (exact h))))
      (is (contains? (:erased (simp/elab-simp-args (a/env) [{:erase "ArgT.D"}]
                                                   (#'simp/default-simp-arg-context (a/env) {})))
                     ["ArgT.D.eq_1" false]))
      (is (fails-with? #"Proof incomplete|made no progress|Type mismatch"
                       '(a/theorem d-eq-erased [h :- (ArgT.P ArgT.a)] (ArgT.P ArgT.D) (simp [-ArgT.D]) (exact h)))))))

(deftest simproc-erasure
  ;; Elab/Tactic/Simp.lean:340-341, 460-461; Simproc.lean:112-113, 153-154
  (let [env (a/env)]
    (is (= #{"Nat.reduceAdd"} (:simproc-erased (simp/elab-simp-args env [{:erase "Nat.reduceAdd"}] {}))))
    (is (= #{"Nat.reduceAdd"} (:simproc-erased (simp/elab-simp-args env ['Nat.reduceAdd {:erase "Nat.reduceAdd"}] {}))))
    (is (= #{} (:simproc-erased (simp/elab-simp-args env [{:erase "Nat.reduceAdd"} 'Nat.reduceAdd] {}))))
    (is (empty? (:erased (simp/elab-simp-args env [{:erase "Nat.reduceAdd"}] {}))))))

(deftest invalid-inverse-arguments
  (testing "a declaration to unfold cannot be refolded (Elab/Tactic/Simp.lean:277-281)"
    (is (fails-with? #"Invalid `←` modifier: `Nat.pred` is a declaration name to be unfolded"
                     '(a/theorem inv-def [n :- Nat] (= Nat n n) (simp [← Nat.pred]))))
    (is (fails-with? #"Invalid `←` modifier: `Nat.zero` is a declaration name to be unfolded"
                     '(a/theorem inv-ctor [n :- Nat] (= Nat n n) (simp [← Nat.zero])))))
  (testing "a rewrite to False cannot be reversed (SimpTheorems.lean:355-357)"
    (is (fails-with? #"Invalid `←` modifier"
                     '(a/theorem inv-ne [a :- Nat, h :- (Not (= Nat a 0))] (= Nat a a) (simp [← h])))))
  (testing "a modified term that is no proof is rejected as such (SimpTheorems.lean:486-488)"
    (is (fails-with? #"Expected a proposition"
                     '(a/theorem inv-nonprop [n :- Nat] (= Nat n n) (simp [← (Nat.succ n)])))))
  (testing "a simproc, a non-propositional local"
    (is (fails-with? #"Invalid `←` modifier: `Nat.reduceAdd` is a simproc"
                     '(a/theorem inv-simproc [n :- Nat] (= Nat n n) (simp [← Nat.reduceAdd]))))
    (is (fails-with? #"not a proposition or let-declaration"
                     '(a/theorem inv-local [n :- Nat] (= Nat n n) (simp [← n])))))
  (testing "`*` takes no modifier, `↑` included"
    (is (fails-with? #"`\*` takes no modifier"
                     '(a/theorem up-star [P :- Prop, h :- P] P (simp [↑ *]))))))

(deftest combined-pre-inverse-argument
  (is (proves? '(a/theorem pre-inv [f :- (=> Nat Nat), g :- (=> Nat Nat), x :- Nat,
                                    h :- (forall [y :- Nat] (= Nat (f y) (g y)))]
                           (= Nat (g x) (f x)) (simp [↓ ← h])))))

(deftest descriptor-fields-survive-elaboration
  (is (= [{:name "Nat.zero_add" :post false :inv false :priority 1200}]
         (:decls (simp/elab-simp-args (a/env) [{:name "Nat.zero_add" :post false :priority 1200}] {})))))

(deftest a-definition-argument-registers-its-equations-in-order
  ;; Elab/Tactic/Simp.lean:283-285 + SimpTheorems.lean:559-591: `simp [f]` adds f's equation
  ;; theorems as entries, so later arguments erase or invert them like any theorem
  (let [env (a/env)
        eq1 (str (first (ansatz.eqns/get-eqns-for? env (ansatz.kernel.name/from-string "List.length"))))
        only (#'simp/default-simp-arg-context env {:only? true})]
    (is (some? eq1))
    (testing "[f, -f.eq_1]: the equation is erased (silently)"
      (let [r (simp/elab-simp-args env ['List.length {:erase eq1}] only)]
        (is (contains? (:erased r) [eq1 false]))
        (is (not-any? :warning (:erase-results r)))
        (is (some #(= eq1 (:name %)) (:decls r)))
        (is (contains? (:to-unfold r) "List.length"))))
    (testing "[← f.eq_1, f]: adding f's forward equation erases the inverse"
      (let [r (simp/elab-simp-args env [{:name eq1 :inv true} 'List.length] only)]
        (is (contains? (:erased r) [eq1 true]))
        (is (not (contains? (:erased r) [eq1 false])))))
    (testing "[f, -f]: only the unfolding is erased; the equations stay (Lean: no toUnfoldThms)"
      (let [r (simp/elab-simp-args env ['List.length {:erase "List.length"}] only)]
        (is (not (contains? (:to-unfold r) "List.length")))
        (is (not (contains? (:erased r) [eq1 false])))))))

(deftest a-location-does-not-simplify-with-its-own-hypothesis
  ;; Lean simpGoal erases the location's own `.fvar` origin
  (is (fails-with? #"made no progress"
                   '(a/theorem star-at-self [F :- (=> Nat Nat), x :- Nat, h :- (= Nat (F x) x)]
                               (= Nat (F x) x) (simp only [*] at h)))))

(deftest an-erased-hypothesis-does-not-discharge
  (is (proves? '(a/theorem disch-star [Q :- Prop, a :- Nat, b :- Nat, h :- Q, t :- (=> Q (= Nat a b))]
                           (= Nat a b) (simp only [* t]))))
  (is (fails-with? #"Proof incomplete|made no progress"
                   '(a/theorem disch-erased [Q :- Prop, a :- Nat, b :- Nat, h :- Q, t :- (=> Q (= Nat a b))]
                               (= Nat a b) (simp only [* -h t])))))

(deftest inherited-definitions-to-unfold-are-unfolded
  ;; Lean toUnfold: an inherited `@[simp] def` unfolds outside `simp only`
  (with-axioms #(-> (argT-env %)
                    (ansatz.kernel.env/check-constant
                     (ansatz.kernel.env/mk-def (ansatz.kernel.name/from-string "ArgT.D2") [] nat (k "ArgT.a")))
                    (ansatz.kernel.env/update-extension :simp-unfold #{} conj "ArgT.D2"))
    (fn []
      (let [goal (ansatz.kernel.expr/app (k "ArgT.P") (k "ArgT.D2"))
            [ps _] (ansatz.tactic.proof/start-proof (a/env) goal)
            after (fn [args opts] (:type (ansatz.tactic.proof/current-goal (simp/simp ps args opts))))]
        (is (= (ansatz.kernel.expr/app (k "ArgT.P") (k "ArgT.a")) (after [] {})))
        (is (= goal (after [] {:only? true})))))))

(deftest a-parenthesized-constant-is-a-declaration
  ;; Lean mkSimpTheoremFromExpr (SimpTheorems.lean:493-495): `(t)` elaborates to the constant
  ;; `t` and goes through mkSimpTheoremFromConst, with the declaration origin
  (with-axioms argT-env
    (fn []
      (testing "[t, ← (t)]: the converse erases the forward rule (no a ↔ b cycle)"
        (is (proves? '(a/theorem paren-conv [h :- (ArgT.P ArgT.a)] (ArgT.P ArgT.b)
                                 (simp only [ArgT.t ← (ArgT.t)]) (exact h)))))
      (testing "[(t), -t]: erasing t erases the parenthesized rule"
        (is (fails-with? #"Proof incomplete|made no progress|Type mismatch"
                         '(a/theorem paren-erase [h :- (ArgT.P ArgT.b)] (ArgT.P ArgT.a)
                                     (simp only [(ArgT.t) -ArgT.t]) (exact h)))))
      (testing "the surface boundary records the declaration origin at the explicit default priority"
        (is (= {:name "ArgT.t" :post true :inv true :priority 1000}
               (simp/term-arg-entry (a/env) (k "ArgT.t") true true)))
        (is (= [{:name "ArgT.t" :post true :inv true :priority 1000}]
               (:decls (simp/elab-simp-args (a/env) [(simp/term-arg-entry (a/env) (k "ArgT.t") true true)] {})))))
      (testing "a programmatic Expr argument stays a proof term"
        (is (= [{:term (k "ArgT.t") :post true :inv false}]
               (:terms (simp/elab-simp-args (a/env) [(k "ArgT.t")] {}))))))))

(deftest a-parenthesized-constant-takes-the-explicit-priority
  ;; Lean mkSimpTheoremFromExpr passes `prio := eval_prio default` (1000) to
  ;; mkSimpTheoremFromConst; the inherited @[simp 100] of t does not apply
  (with-axioms #(-> (argT-env %)
                    (ax* "ArgT.c" nat)
                    (ax* "ArgT.s" (eqn* (k "ArgT.a") (k "ArgT.c")))
                    (ansatz.kernel.env/update-extension :simp-lemmas #{} into ["ArgT.t" "ArgT.s"])
                    (ansatz.kernel.env/update-extension :simp-priorities {} assoc "ArgT.t" 100 "ArgT.s" 500))
    (fn []
      (testing "inherited only: s (500) wins over t (100): P a ↦ P c"
        (is (proves? '(a/theorem paren-prio-inh [h :- (ArgT.P ArgT.c)] (ArgT.P ArgT.a) (simp) (exact h)))))
      (testing "[(t)]: t at 1000 wins: P a ↦ P b"
        (is (proves? '(a/theorem paren-prio [h :- (ArgT.P ArgT.b)] (ArgT.P ArgT.a) (simp [(ArgT.t)]) (exact h)))))
      (testing "[t]: a named theorem takes the same explicit priority: P a ↦ P b"
        (is (proves? '(a/theorem bare-prio [h :- (ArgT.P ArgT.b)] (ArgT.P ArgT.a) (simp [ArgT.t]) (exact h))))))))

(deftest bare-and-parenthesized-inverses-take-the-explicit-priority
  ;; t : a = b at @[simp 100], s : b = c at @[simp 500]; on P b both `← t` and `← (t)` register
  ;; the inverse at 1000 (Elab/Tactic/Simp.lean:274, SimpTheorems.lean:453), so b ↦ a wins
  (with-axioms #(-> (argT-env %)
                    (ax* "ArgT.c" nat)
                    (ax* "ArgT.s2" (eqn* (k "ArgT.b") (k "ArgT.c")))
                    (ansatz.kernel.env/update-extension :simp-lemmas #{} into ["ArgT.s2"])
                    (ansatz.kernel.env/update-extension :simp-priorities {} assoc "ArgT.t" 100 "ArgT.s2" 500))
    (fn []
      (is (proves? '(a/theorem inv-bare [h :- (ArgT.P ArgT.a)] (ArgT.P ArgT.b) (simp [← ArgT.t]) (exact h))))
      (is (proves? '(a/theorem inv-paren [h :- (ArgT.P ArgT.a)] (ArgT.P ArgT.b) (simp [← (ArgT.t)]) (exact h)))))))

(deftest a-proof-term-descriptor-keeps-its-priority
  ;; {:term t :priority 100} against s : a = c at 500 under simp only: s wins, P a ↦ P c
  (with-axioms #(-> (argT-env %) (ax* "ArgT.c" nat) (ax* "ArgT.s" (eqn* (k "ArgT.a") (k "ArgT.c"))))
    (fn []
      (let [goal (ansatz.kernel.expr/app (k "ArgT.P") (k "ArgT.a"))
            [ps _] (ansatz.tactic.proof/start-proof (a/env) goal)
            after (fn [args] (:type (ansatz.tactic.proof/current-goal (simp/simp ps args {:only? true}))))]
        (is (= (ansatz.kernel.expr/app (k "ArgT.P") (k "ArgT.c"))
               (after [{:term (k "ArgT.t") :priority 100} {:name "ArgT.s" :priority 500}])))
        (is (= (ansatz.kernel.expr/app (k "ArgT.P") (k "ArgT.b"))
               (after [{:term (k "ArgT.t") :priority 1000} {:name "ArgT.s" :priority 500}])))
        (testing "a nil :priority is the default, 1000"
          (is (= (ansatz.kernel.expr/app (k "ArgT.P") (k "ArgT.b"))
                 (after [{:term (k "ArgT.t") :priority nil} {:name "ArgT.s" :priority 500}]))))))))

(defn- simp-target
  "The goal after `simp/simp ps args opts` on `goal`, or :no-progress."
  [goal args opts]
  (let [[ps _] (ansatz.tactic.proof/start-proof (a/env) goal)]
    (try (:type (ansatz.tactic.proof/current-goal (simp/simp ps args opts)))
         (catch clojure.lang.ExceptionInfo ex
           (if (re-find #"no progress" (ex-message ex)) :no-progress (throw ex))))))

(deftest a-programmatic-constant-keeps-its-universe-levels
  ;; t.{u} : a.{u} = b.{u}; the Expr t.{0} does not rewrite a.{1}
  (let [u (ansatz.kernel.level/param (ansatz.kernel.name/from-string "u"))
        one (ansatz.kernel.level/succ ansatz.kernel.level/zero)
        ku (fn [s l] (ansatz.kernel.expr/const' (ansatz.kernel.name/from-string s) [l]))
        poly (fn [env n ty] (ansatz.kernel.env/check-constant
                             env (ansatz.kernel.env/mk-axiom (ansatz.kernel.name/from-string n)
                                                             [(ansatz.kernel.name/from-string "u")] ty)))]
    (with-axioms #(-> (argT-env %)
                      (poly "ArgU.a" nat) (poly "ArgU.b" nat)
                      (poly "ArgU.t" (eqn* (ku "ArgU.a" u) (ku "ArgU.b" u))))
      (fn []
        (let [goal (ansatz.kernel.expr/app (k "ArgT.P") (ku "ArgU.a" one))]
          (is (contains? #{:no-progress goal}
                         (simp-target goal [(ku "ArgU.t" ansatz.kernel.level/zero)] {:only? true})))
          (is (= (ansatz.kernel.expr/app (k "ArgT.P") (ku "ArgU.b" one))
                 (simp-target goal [(ku "ArgU.t" one)] {:only? true}))))))))

(deftest a-programmatic-constant-keeps-its-kernel-name
  ;; the one-component name `a.b` (x = y) and the two-component a.b (x = z) are distinct
  (let [one-comp (ansatz.kernel.name/mk-str (ansatz.kernel.name/anonymous) "ArgN.a.b")
        two-comp (ansatz.kernel.name/from-string "ArgN.a.b")]
    (is (not= one-comp two-comp))
    (with-axioms #(-> (argT-env %)
                      (ax* "ArgN.x" nat) (ax* "ArgN.y" nat) (ax* "ArgN.z" nat)
                      (ansatz.kernel.env/check-constant (ansatz.kernel.env/mk-axiom one-comp [] (eqn* (k "ArgN.x") (k "ArgN.y"))))
                      (ansatz.kernel.env/check-constant (ansatz.kernel.env/mk-axiom two-comp [] (eqn* (k "ArgN.x") (k "ArgN.z")))))
      (fn []
        (is (= (ansatz.kernel.expr/app (k "ArgT.P") (k "ArgN.y"))
               (simp-target (ansatz.kernel.expr/app (k "ArgT.P") (k "ArgN.x"))
                            [(ansatz.kernel.expr/const' one-comp [])] {:only? true})))))))

(defn- argF-env
  "F := a with its equation F.eq_1 : F = a, and an inherited @[simp 500] rule F_b : F = b."
  [env]
  (-> (argT-env env)
      (ansatz.kernel.env/check-constant
       (ansatz.kernel.env/mk-def (ansatz.kernel.name/from-string "ArgT.F") [] nat (k "ArgT.a")))
      (ansatz.kernel.env/check-constant
       (ansatz.kernel.env/mk-thm (ansatz.kernel.name/from-string "ArgT.F.eq_1") [] (eqn* (k "ArgT.F") (k "ArgT.a"))
                                 (ansatz.kernel.expr/app* (ansatz.kernel.expr/const' (ansatz.kernel.name/from-string "Eq.refl")
                                                                                     [(ansatz.kernel.level/succ ansatz.kernel.level/zero)])
                                                          nat (k "ArgT.a"))))
      (ansatz.eqns/register-eqn-thms "ArgT.F" ["ArgT.F.eq_1"] [])
      (ax* "ArgT.F_b" (eqn* (k "ArgT.F") (k "ArgT.b")))
      (ansatz.kernel.env/update-extension :simp-lemmas #{} conj "ArgT.F_b")
      (ansatz.kernel.env/update-extension :simp-priorities {} assoc "ArgT.F_b" 500)))

(deftest a-re-registered-equation-takes-its-new-priority
  ;; Lean DiscrTree insertVal (DiscrTree/Basic.lean:135-148): `f` re-adds f.eq_1 at priority 100,
  ;; replacing the explicit entry (1000), so the inherited F_b (500) wins once `-f` drops the unfolding
  (with-axioms argF-env
    (fn []
      (testing "[F.eq_1, F, -F]: F ↦ b"
        (is (proves? '(a/theorem reprio-b [h :- (ArgT.P ArgT.b)] (ArgT.P ArgT.F)
                                 (simp [ArgT.F.eq_1 ArgT.F -ArgT.F]) (exact h)))))
      (testing "[F, -F, F.eq_1]: the explicit entry comes last and wins at 1000: F ↦ a"
        (is (proves? '(a/theorem reprio-a [h :- (ArgT.P ArgT.a)] (ArgT.P ArgT.F)
                                 (simp [ArgT.F -ArgT.F ArgT.F.eq_1]) (exact h))))))))

(deftest an-un-erased-origin-keeps-an-earlier-explicit-priority
  ;; Lean eraseCore leaves the tree entry (SimpTheorems.lean:612-622): in [↓ h, -h, h] the
  ;; explicit ↓ h (1000) stays, so it beats the inherited pre k (500); the inherited pre h (100)
  ;; masked by the inherited ← h does not come back over it
  (with-axioms #(let [env (-> (argT-env %)
                              (ax* "ArgD.F" (ansatz.kernel.expr/arrow nat nat))
                              (ax* "ArgD.G" (ansatz.kernel.expr/arrow nat nat))
                              (ax* "ArgD.K" (ansatz.kernel.expr/arrow nat nat))
                              (ax* "ArgD.x" nat))
                      ap (fn [f] (ansatz.kernel.expr/app (k f) (k "ArgD.x")))
                      env (-> env
                              (ax* "ArgD.h" (eqn* (ap "ArgD.F") (ap "ArgD.G")))
                              (ax* "ArgD.k" (eqn* (ap "ArgD.F") (ap "ArgD.K"))))]
                  (first (ansatz.attrs/import-attr-tuples
                          env [["simp" "ArgD.h" nil 100 {:post false :inv false}]
                               ["simp" "ArgD.h" nil 100 {:post true :inv true}]
                               ["simp" "ArgD.k" nil 500 {:post false :inv false}]]
                          {:present? (constantly true)})))
    (fn []
      (is (proves? '(a/theorem unerase-prio [hp :- (ArgT.P (ArgD.G ArgD.x))] (ArgT.P (ArgD.F ArgD.x))
                               (simp [↓ ArgD.h -ArgD.h ArgD.h]) (exact hp))))
      (testing "the inherited pre k wins when only the inherited pre h is revealed"
        (is (proves? '(a/theorem unerase-inherited [hp :- (ArgT.P (ArgD.K ArgD.x))] (ArgT.P (ArgD.F ArgD.x))
                                 (simp [ArgD.h]) (exact hp))))))))

(deftest the-pre-modifier-through-the-tactic
  ;; pre: K (F x) = 0 fires before F x ↦ G x; as a post rule its match is gone (Lean behaviour)
  (let [thm (fn [args] (list 'a/theorem (gensym "pre-surface")
                             '[F :- (=> Nat Nat), G :- (=> Nat Nat), K :- (=> Nat Nat), x :- Nat,
                               h :- (forall [y :- Nat] (= Nat (K (F y)) 0)),
                               t :- (forall [y :- Nat] (= Nat (F y) (G y)))]
                             '(= Nat (K (F x)) 0)
                             (list 'simp 'only args)))]
    (is (proves? (thm '[↓ h t])))
    (is (fails-with? #"Proof incomplete|made no progress" (thm '[h t])))))

(deftest a-prop-domain-that-simplifies-goes-through-forall-prop-domain-congr
  ;; Lean simpForall (Main.lean:369-402): the dependent ∀ h : succ n = 0, Q h has its domain
  ;; rewritten to False, then ∀ h : False, _ is True
  (is (proves? '(a/theorem forall-prop-domain [n :- Nat, Q :- (=> (= Nat (Nat.succ n) 0) Prop)]
                           (forall [h :- (= Nat (Nat.succ n) 0)] (Q h))
                           (simp)))))
