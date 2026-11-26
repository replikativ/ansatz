(ns ansatz.tactic.simp-pre-test
  "Pre rules (`@[simp ↓]`, `simp [↓ h]`) and the erased set: Lean 4.36.0 SimpTheorems.lean
   {pre, post, erased} and Rewrite.lean rewritePre/rewritePost/inErasedSet. Cases adapted from
   Lean's tests/elab/4290.lean and eraseSimp.lean; proofs are re-checked by the kernel."
  (:require [ansatz.test-env :as test-env]
            [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.simp :as simp]
            [ansatz.tactic.discr-tree :as dt]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.simp-index :as si]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(defn- require-env []
  (or @test-env/checked-bundled-init-env (throw (ex-info "bundled Init unavailable" {}))))

(def ^:private nat (e/const' (name/from-string "Nat") []))
(def ^:private prop (e/sort' lvl/zero))
(defn- c [s] (e/const' (name/from-string s) []))
(defn- eq-at [ty x y] (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) ty x y))
(defn- eqn [x y] (eq-at nat x y))
(defn- ax [env n ty] (env/check-constant env (env/mk-axiom (name/from-string n) [] ty)))

(defn- pre-env []
  (-> (require-env)
      (ax "SimpPre.F" (e/arrow nat nat)) (ax "SimpPre.G" (e/arrow nat nat))
      (ax "SimpPre.H" (e/arrow nat nat))
      (ax "SimpPre.P" (e/arrow nat prop)) (ax "SimpPre.a" nat)
      ;; post_rule : ∀ x, F x = G x
      (ax "SimpPre.post_rule" (e/forall' "x" nat (eqn (e/app (c "SimpPre.F") (e/bvar 0))
                                                      (e/app (c "SimpPre.G") (e/bvar 0))) :default))
      ;; pre_rule : ∀ x, P (G x)
      (ax "SimpPre.pre_rule" (e/forall' "x" nat (e/app (c "SimpPre.P") (e/app (c "SimpPre.G") (e/bvar 0)))
                                        :default))
      ;; pre_rule_f : ∀ x, P (F x) — matches only before F x is rewritten
      (ax "SimpPre.pre_rule_f" (e/forall' "x" nat (e/app (c "SimpPre.P") (e/app (c "SimpPre.F") (e/bvar 0)))
                                          :default))
      ;; 4290.lean: foo_eq_bar : foo = bar, de : d = e
      (ax "SimpPre.foo" nat) (ax "SimpPre.bar" nat)
      (ax "SimpPre.foo_eq_bar" (eqn (c "SimpPre.foo") (c "SimpPre.bar")))
      (ax "SimpPre.d" nat) (ax "SimpPre.e" nat)
      (ax "SimpPre.de" (eqn (c "SimpPre.d") (c "SimpPre.e")))))

(defn- run [env entries expr & [state]]
  (let [st (tc/mk-tc-state env)
        [post pre] (simp/build-simp-indexes st env (simp/make-simp-lemmas env entries))]
    (simp/simp-expr-result st env post expr 20 (merge {:pre-index pre} state))))

(defn- checks?
  "The rewrite's proof kernel-checks; a missing proof only for a definitional step."
  [env lhs result]
  (let [ty (tc/infer-type (tc/mk-tc-state env) lhs)
        goal (eq-at ty lhs (:expr result))]
    (if (:proof? result)
      (env/verifies? env goal (:proof? result))
      (env/verifies? env goal (e/app* (e/const' (name/from-string "Eq.refl") [(lvl/succ lvl/zero)]) ty lhs)))))

(deftest pre-rules-go-into-the-pre-tree
  (let [env (pre-env)
        st (tc/mk-tc-state env)
        rules (simp/make-simp-lemmas env [{:name "SimpPre.pre_rule" :post false} "SimpPre.post_rule"])
        [post pre] (simp/build-simp-indexes st env rules)]
    (is (= [false true] (mapv :post rules)))
    (is (some? pre))
    (is (= 1 (count (#'simp/lookup-lemmas st env pre (e/app (c "SimpPre.P") (e/app (c "SimpPre.G") (c "SimpPre.a")))))))
    (is (empty? (#'simp/lookup-lemmas st env post (e/app (c "SimpPre.P") (e/app (c "SimpPre.G") (c "SimpPre.a"))))))))

(deftest a-pre-rule-is-not-tried-in-the-post-phase
  (testing "single pass: after F a ↦ G a, the post phase does not see a ↓ rule (Rewrite.lean:395-399)"
    (let [env (pre-env)
          goal (e/app (c "SimpPre.P") (e/app (c "SimpPre.F") (c "SimpPre.a")))
          as-pre (run env [{:name "SimpPre.pre_rule" :post false} "SimpPre.post_rule"] goal {:single-pass? true})
          as-post (run env ["SimpPre.pre_rule" "SimpPre.post_rule"] goal {:single-pass? true})]
      (is (= (e/app (c "SimpPre.P") (e/app (c "SimpPre.G") (c "SimpPre.a"))) (:expr as-pre)))
      (is (= (c "True") (:expr as-post)))
      (is (checks? env goal as-pre))
      (is (checks? env goal as-post))))
  (testing "without single pass the changed term is visited again and the pre rule fires"
    (let [env (pre-env)
          goal (e/app (c "SimpPre.P") (e/app (c "SimpPre.F") (c "SimpPre.a")))
          r (run env [{:name "SimpPre.pre_rule" :post false} "SimpPre.post_rule"] goal)]
      (is (= (c "True") (:expr r)))
      (is (checks? env goal r)))))

(deftest pre-rules-fire-before-the-arguments-are-visited
  (let [env (pre-env)
        goal (e/app (c "SimpPre.P") (e/app (c "SimpPre.G") (c "SimpPre.a")))
        trace (atom [])
        r (binding [simp/*simp-trace* trace]
            (run env [{:name "SimpPre.pre_rule" :post false}] goal))]
    (is (= (c "True") (:expr r)))
    (is (= [{:phase :pre :origin "↓ SimpPre.pre_rule"}]
           (mapv #(select-keys % [:phase :origin]) (filter :phase @trace))))))

(deftest erased-rules-are-skipped
  (testing "eraseSimp.lean ex4: `simp [-Nat.zero_add]` does not rewrite 0 + a"
    (let [env (require-env)
          a (e/fvar 991201)
          st (tc/attach-lctx (tc/mk-tc-state env) {991201 {:type nat :tag :local}})
          rules (simp/make-simp-lemmas env ["Nat.zero_add"])
          ;; the rule's own lhs `0 + n` at n := a
          goal (e/instantiate1 (:lhs-pattern (first rules)) a)
          [post _] (simp/build-simp-indexes st env rules)]
      (is (= a (:expr (simp/simp-expr-result st env post goal))))
      (is (= goal (:expr (simp/simp-expr-result st env post goal 20 {:erased #{["Nat.zero_add" false]}}))))
      (testing "erasing the converse origin does not erase the forward rule"
        (is (= a (:expr (simp/simp-expr-result st env post goal 20 {:erased #{["Nat.zero_add" true]}}))))))))

(deftest inverse-with-the-forward-rule-erased-terminates
  (testing "4290.lean: @[simp] foo_eq_bar; simp [← foo_eq_bar] turns foo = H bar into foo = H foo"
    (let [env (pre-env)
          goal (eqn (c "SimpPre.foo") (e/app (c "SimpPre.H") (c "SimpPre.bar")))
          ;; Lean addSimpTheorem → eraseFwdIfBwd (SimpTheorems.lean:634-652) erases the forward rule
          r (run env ["SimpPre.foo_eq_bar" {:name "SimpPre.foo_eq_bar" :inv true}] goal
                 {:erased #{["SimpPre.foo_eq_bar" false]}})]
      (is (= (eqn (c "SimpPre.foo") (e/app (c "SimpPre.H") (c "SimpPre.foo"))) (:expr r)))
      (is (checks? env goal r))))
  (testing "4290.lean: @[simp↓] de; simp [↓←de] turns d = H e into d = H d"
    (let [env (pre-env)
          goal (eqn (c "SimpPre.d") (e/app (c "SimpPre.H") (c "SimpPre.e")))
          r (run env [{:name "SimpPre.de" :post false} {:name "SimpPre.de" :post false :inv true}] goal
                 {:erased #{["SimpPre.de" false]}})]
      (is (= (eqn (c "SimpPre.d") (e/app (c "SimpPre.H") (c "SimpPre.d"))) (:expr r)))
      (is (checks? env goal r)))))

(deftest simp-all-target-keeps-the-erasure
  ;; Lean SimpAll uses one Simp.Context for hypotheses and target; erasing the forward
  ;; foo_eq_bar beside its inverse must hold in the target pass too, or foo ↦ bar ↦ foo loops.
  (let [env (pre-env)
        args ["SimpPre.foo_eq_bar" {:name "SimpPre.foo_eq_bar" :inv true}]
        opts {:erased #{["SimpPre.foo_eq_bar" false]}}
        expected (eqn (c "SimpPre.foo") (e/app (c "SimpPre.H") (c "SimpPre.foo")))]
    (testing "no hypotheses"
      (let [[ps _] (proof/start-proof env (eqn (c "SimpPre.foo") (e/app (c "SimpPre.H") (c "SimpPre.bar"))))
            ps (simp/simp-all ps args opts)]
        (is (= expected (:type (proof/current-goal ps))))))
    (testing "a hypothesis changes before the target pass"
      (let [hyp (eqn (e/app (c "SimpPre.H") (c "SimpPre.bar")) (c "SimpPre.a"))
            [ps _] (proof/start-proof env (e/arrow hyp (eqn (c "SimpPre.foo") (e/app (c "SimpPre.H") (c "SimpPre.bar")))))
            ps (basic/intro ps "h")
            ps (simp/simp-all ps args opts)
            g (proof/current-goal ps)]
        ;; the replaced hypothesis h' : H foo = a sits next to h; the target pass (inverse rule,
        ;; forward erased) reaches foo = H foo, which h' then rewrites to foo = a
        (is (some #(and (= "h'" (str (:name %)))
                        (= (eqn (e/app (c "SimpPre.H") (c "SimpPre.foo")) (c "SimpPre.a")) (:type %)))
                  (vals (:lctx g))))
        (is (= (eqn (c "SimpPre.foo") (c "SimpPre.a")) (:type g)))))))

(deftest simp-all-skips-an-erased-hypothesis
  ;; SimpAll.lean:39-53: an erased local is not simplified (no h') and not used
  (let [env (pre-env)
        hyp (e/app (c "SimpPre.P") (e/app (c "SimpPre.F") (c "SimpPre.a")))
        target (e/app (c "SimpPre.P") (e/app (c "SimpPre.G") (c "SimpPre.a")))
        [ps _] (proof/start-proof env (e/arrow hyp target))
        ps (basic/intro ps "h")
        h-id (key (first (filter #(= "h" (str (:name (val %)))) (:lctx (proof/current-goal ps)))))
        ps (try (simp/simp-all ps ["SimpPre.post_rule"] {:erased #{[:fvar h-id]}})
                (catch clojure.lang.ExceptionInfo _ ps))
        g (proof/current-goal ps)]
    (is (some? g))
    (is (= target (:type g)))
    (is (not-any? #(= "h'" (str (:name %))) (vals (:lctx g))))
    (is (= hyp (:type (get (:lctx g) h-id))))))

(deftest an-erased-hypothesis-does-not-discharge-a-condition
  ;; h : P a and conditional : P a → F a = G a; with h erased the condition stays open (Lean
  ;; simp_all only [conditional, -h])
  (let [fa (e/app (c "SimpPre.F") (c "SimpPre.a"))
        ga (e/app (c "SimpPre.G") (c "SimpPre.a"))
        env (ax (pre-env) "SimpPre.conditional" (e/arrow (e/app (c "SimpPre.P") (c "SimpPre.a")) (eqn fa ga)))
        [ps _] (proof/start-proof env (e/arrow (e/app (c "SimpPre.P") (c "SimpPre.a")) (eqn fa ga)))
        ps (basic/intro ps "h")
        h-id (key (first (filter #(= "h" (str (:name (val %)))) (:lctx (proof/current-goal ps)))))
        run (fn [opts] (simp/simp-all ps ["SimpPre.conditional"] (merge {:only? true} opts)))
        erased (run {:erased #{[:fvar h-id]}})]
    (is (proof/solved? (run {})) "h discharges the condition")
    (is (= (eqn fa ga) (:type (proof/current-goal erased))) "the erased h does not")))

(deftest quantified-contextual-hypotheses-are-erasable
  ;; Lean gives every contextual hypothesis the origin `.fvar h`, whatever its telescope.
  (let [env (pre-env)
        hyp (e/forall' "x" nat (eqn (e/app (c "SimpPre.F") (e/bvar 0)) (e/app (c "SimpPre.G") (e/bvar 0))) :default)
        [ps _] (proof/start-proof env (e/arrow hyp (eqn (e/app (c "SimpPre.F") (c "SimpPre.a")) (c "SimpPre.a"))))
        ps (basic/intro ps "h")
        h-id (key (first (filter #(= "h" (str (:name (val %)))) (:lctx (proof/current-goal ps)))))
        after (fn [opts] (:type (proof/current-goal (simp/simp ps [] (merge {:contextual? true} opts)))))]
    (is (= (eqn (e/app (c "SimpPre.G") (c "SimpPre.a")) (c "SimpPre.a")) (after {})))
    (is (= (eqn (e/app (c "SimpPre.F") (c "SimpPre.a")) (c "SimpPre.a"))
           (try (after {:erased #{[:fvar h-id]}})
                (catch clojure.lang.ExceptionInfo _ (:type (proof/current-goal ps))))))))

(deftest one-forward-origin-key-erases-both-phases
  ;; Lean BEq Origin ignores the phase: erasing [n false] hides n's pre and post entries
  (let [env (pre-env)
        goal (e/app (c "SimpPre.F") (c "SimpPre.a"))
        entries [{:name "SimpPre.post_rule" :post false} "SimpPre.post_rule"]]
    (is (= (e/app (c "SimpPre.G") (c "SimpPre.a")) (:expr (run env entries goal))))
    (is (= goal (:expr (run env entries goal {:erased #{["SimpPre.post_rule" false]}}))))))

(deftest erasure-covers-the-lazy-index
  ;; A forward rule served only by the persistent index (lookup-lemmas' :ext-trie) is filtered
  ;; by origin like an eager one (Lean inErasedSet, Rewrite.lean:283-284).
  (let [env (env/update-extension (pre-env) :simp-lemmas #{} conj "SimpPre.post_rule")
        st (tc/mk-tc-state env)
        trie (si/build-simp-trie (si/key-entries-artifact (si/lemma-keys ["SimpPre.post_rule"] env #(env/lookup env (name/from-string %)))))
        [post _] (simp/build-simp-indexes st env [])
        goal (e/app (c "SimpPre.F") (c "SimpPre.a"))
        run (fn [state] (simp/simp-expr-result st env post goal 20 (merge {:ext-trie trie} state)))
        fired (run {})]
    (is (= (e/app (c "SimpPre.G") (c "SimpPre.a")) (:expr fired)))
    (is (checks? env goal fired))
    (is (= goal (:expr (run {:erased #{["SimpPre.post_rule" false]}}))))))

(deftest a-pre-rule-wins-over-a-higher-priority-post-rule
  ;; Lean visits pre before post, whatever the priorities: both rules match F a.
  (let [env (-> (pre-env)
                (ax "SimpPre.F_to_H" (e/forall' "x" nat (eqn (e/app (c "SimpPre.F") (e/bvar 0))
                                                             (e/app (c "SimpPre.H") (e/bvar 0))) :default)))
        goal (e/app (c "SimpPre.F") (c "SimpPre.a"))
        r (run env [{:name "SimpPre.F_to_H" :post false :priority 10} {:name "SimpPre.post_rule" :priority 5000}] goal)]
    (is (= (e/app (c "SimpPre.H") (c "SimpPre.a")) (:expr r)))
    (is (checks? env goal r))))

(deftest default-rules-are-not-tried-top-down
  ;; Lean Rewrite.lean:536-547: preDefault rewrites with SimpTheorems.pre only; the default
  ;; @[simp] set is post. A rule matching only the unsimplified term must be `↓` to fire.
  (let [env (pre-env)
        goal (e/app (c "SimpPre.P") (e/app (c "SimpPre.F") (c "SimpPre.a")))
        as-pre (run env [{:name "SimpPre.pre_rule_f" :post false} "SimpPre.post_rule"] goal)
        as-post (run env ["SimpPre.pre_rule_f" "SimpPre.post_rule"] goal)]
    (is (= (c "True") (:expr as-pre)))
    (is (checks? env goal as-pre))
    (is (= (e/app (c "SimpPre.P") (e/app (c "SimpPre.G") (c "SimpPre.a"))) (:expr as-post)))
    (is (checks? env goal as-post))))

(deftest default-rules-served-by-the-persistent-index-stay-post
  ;; the same discriminator with the default rule served only by a captured trie
  (let [env (env/update-extension (pre-env) :simp-lemmas #{} into ["SimpPre.pre_rule_f" "SimpPre.post_rule"])
        st (tc/mk-tc-state env)
        trie (si/build-simp-trie (si/key-entries-artifact
                                  (si/lemma-keys ["SimpPre.pre_rule_f" "SimpPre.post_rule"] env
                                                 #(env/lookup env (name/from-string %)))))
        [post _] (simp/build-simp-indexes st env [])
        goal (e/app (c "SimpPre.P") (e/app (c "SimpPre.F") (c "SimpPre.a")))
        r (simp/simp-expr-result st env post goal 20 {:ext-trie trie})]
    (is (= (e/app (c "SimpPre.P") (e/app (c "SimpPre.G") (c "SimpPre.a"))) (:expr r)))
    (is (checks? env goal r))))

(deftest ite-selects-its-branch-before-visiting-it
  ;; Lean reduceIte is `builtin_simproc ↓` (BuiltinSimprocs/Core.lean:15): with an opaque
  ;; `Decidable True` instance the condition simp's to True and the dead branch, whose rules
  ;; u ↦ v ↦ u would cycle, is never visited.
  (let [env (-> (pre-env)
                (ax "SimpPre.dec" (e/app (c "Decidable") (c "True")))
                (ax "SimpPre.u" nat) (ax "SimpPre.v" nat)
                (ax "SimpPre.uv" (eqn (c "SimpPre.u") (c "SimpPre.v")))
                (ax "SimpPre.vu" (eqn (c "SimpPre.v") (c "SimpPre.u"))))
        st (tc/mk-tc-state env)
        goal (e/app* (e/const' (name/from-string "ite") [(lvl/succ lvl/zero)]) nat (c "True") (c "SimpPre.dec")
                     (e/lit-nat 0) (c "SimpPre.u"))
        [post pre] (simp/build-simp-indexes st env (simp/make-simp-lemmas env ["SimpPre.uv" "SimpPre.vu"]))
        r (simp/simp-expr-result st env post goal 20 {:pre-index pre})]
    (is (= (e/lit-nat 0) (:expr r)))
    (is (checks? env goal r))))

(deftest rules-indexed-under-a-lambda-stay-reachable
  ;; Lean's reduceStep does no function eta (Main.lean:222): `P (fun x => F x)` is not first
  ;; contracted to `P F`, so a rule stated on the lambda still matches.
  (let [nn (e/arrow nat nat)
        lam (e/lam "x" nat (e/app (c "SimpPre.F") (e/bvar 0)) :default)
        env (-> (pre-env)
                (ax "SimpPre.Q" (e/arrow nn prop))
                (ax "SimpPre.q_lam" (e/app (c "SimpPre.Q") lam)))
        st (tc/mk-tc-state env)
        goal (e/app (c "SimpPre.Q") lam)
        [post _] (simp/build-simp-indexes st env (simp/make-simp-lemmas env ["SimpPre.q_lam"]))
        r (simp/simp-expr-result st env post goal)]
    (is (= (c "True") (:expr r)))
    (is (checks? env goal r))))

(deftest rules-on-a-bare-function-match-its-eta-expansion
  ;; Lean keys patterns and queries modulo eta (DiscrTree/Main.lean:204-210): h : Q F rewrites
  ;; Q (fun x => F x), and the lambda spelling keeps working (previous test)
  (let [nn (e/arrow nat nat)
        lam (e/lam "x" nat (e/app (c "SimpPre.F") (e/bvar 0)) :default)
        env (-> (pre-env)
                (ax "SimpPre.Q" (e/arrow nn prop))
                (ax "SimpPre.q_fn" (e/app (c "SimpPre.Q") (c "SimpPre.F"))))
        st (tc/mk-tc-state env)
        goal (e/app (c "SimpPre.Q") lam)
        [post _] (simp/build-simp-indexes st env (simp/make-simp-lemmas env ["SimpPre.q_fn"]))
        r (simp/simp-expr-result st env post goal)]
    (is (= (c "True") (:expr r)))
    (is (checks? env goal r))))

(deftest an-explicit-unmodified-simproc-runs-post
  ;; simp only [reduceIte, h] with h : ite True d u v = w: Lean adds reduceIte post, so the
  ;; theorem on the whole conditional fires first
  (let [env (-> (pre-env)
                (ax "SimpPre.dec" (e/app (c "Decidable") (c "True")))
                (ax "SimpPre.u" nat) (ax "SimpPre.v" nat) (ax "SimpPre.w" nat))
        ite-uv (e/app* (e/const' (name/from-string "ite") [(lvl/succ lvl/zero)]) nat (c "True") (c "SimpPre.dec")
                       (c "SimpPre.u") (c "SimpPre.v"))
        env (ax env "SimpPre.h_ite" (eqn ite-uv (c "SimpPre.w")))
        r (run env ["SimpPre.h_ite"] ite-uv {:simprocs? false :simproc-names #{"reduceIte"}})]
    (is (= (c "SimpPre.w") (:expr r)))
    (is (checks? env ite-uv r))
    (testing "with the default (pre) registration the branch is selected first"
      (is (= (c "SimpPre.u") (:expr (run env ["SimpPre.h_ite"] ite-uv {})))))))

(deftest ite-without-helper-theorems-falls-back-to-definitional-selection
  ;; an env lacking ite_eq_left_of_eq_true/ite_cond_eq_true: select only definitionally
  (let [env (pre-env)
        missing #{"ite_eq_left_of_eq_true" "ite_cond_eq_true"}
        decide-true (e/app* (c "Decidable.isTrue") (c "True") (c "True.intro"))
        goal (e/app* (e/const' (name/from-string "ite") [(lvl/succ lvl/zero)]) nat (c "True") decide-true
                     (c "SimpPre.a") (e/lit-nat 0))
        lookup env/lookup]
    (with-redefs [env/lookup (fn [en n] (when-not (contains? missing (name/->string n)) (lookup en n)))]
      (let [r (run env [] goal {})]
        (is (= (c "SimpPre.a") (:expr r)))
        (is (nil? (:proof? r)))))
    (testing "the constructor decides it: Eq.refl kernel-checks the selection"
      (is (checks? env goal {:expr (c "SimpPre.a")})))))

(deftest function-valued-dite-false-branch-with-extra-argument
  (let [env (-> (pre-env) (ax "SimpPre.x" nat) (ax "SimpPre.g2" (e/arrow nat nat))
                (ax "SimpPre.dec_any" (e/forall' "p" prop (e/app (c "Decidable") (e/bvar 0)) :default)))
        nn (e/arrow nat nat)
        cnd (eqn (e/lit-nat 1) (e/lit-nat 2))
        f-dite (e/app* (e/const' (name/from-string "dite") [(lvl/succ lvl/zero)]) nn cnd
                       (e/app (c "SimpPre.dec_any") cnd)
                       (e/lam "h" cnd (e/lam "y" nat (e/lit-nat 0) :default) :default)
                       (e/lam "h" (e/app (c "Not") cnd) (c "SimpPre.g2") :default))
        goal (e/app f-dite (c "SimpPre.x"))
        r (run env [] goal {})]
    (is (= (e/app (c "SimpPre.g2") (c "SimpPre.x")) (:expr r)))
    (is (checks? env goal r))))

(deftest eta-found-rules-share-one-priority-order
  ;; Lean collects the candidates of the (eta-normalized) keys and sorts them together
  ;; (Rewrite.lean:214-220): on R (fun x => F x) the high-priority R F = 0 wins over the cycling
  ;; low-priority R f = S f / S f = R f that the raw lookup finds first
  (let [nn (e/arrow nat nat)
        lam (e/lam "x" nat (e/app (c "SimpPre.F") (e/bvar 0)) :default)
        env (-> (pre-env)
                (ax "SimpPre.R" (e/arrow nn nat)) (ax "SimpPre.S" (e/arrow nn nat))
                (ax "SimpPre.rs" (e/forall' "f" nn (eqn (e/app (c "SimpPre.R") (e/bvar 0))
                                                        (e/app (c "SimpPre.S") (e/bvar 0))) :default))
                (ax "SimpPre.sr" (e/forall' "f" nn (eqn (e/app (c "SimpPre.S") (e/bvar 0))
                                                        (e/app (c "SimpPre.R") (e/bvar 0))) :default))
                (ax "SimpPre.rF" (eqn (e/app (c "SimpPre.R") (c "SimpPre.F")) (e/lit-nat 0))))
        goal (e/app (c "SimpPre.R") lam)
        r (run env [{:name "SimpPre.rs" :priority 10} {:name "SimpPre.sr" :priority 10}
                    {:name "SimpPre.rF" :priority 2000}] goal)]
    (is (= (e/lit-nat 0) (:expr r)))
    (is (checks? env goal r))))

(deftest eta-lookup-reaches-arguments-of-a-high-arity-application
  ;; eta is normalized at every keyed node, however long the application spine: a rule on
  ;; Q F a … a (12 trailing arguments) rewrites Q (fun x => F x) a … a — eager index and both
  ;; readable trie encodings
  (let [nn (e/arrow nat nat)
        lam (e/lam "x" nat (e/app (c "SimpPre.F") (e/bvar 0)) :default)
        args (repeat 12 (c "SimpPre.a"))
        q-ty (e/arrow nn (reduce (fn [t _] (e/arrow nat t)) prop args))
        env (-> (pre-env)
                (ax "SimpPre.Qhi" q-ty)
                (ax "SimpPre.q_hi" (apply e/app* (c "SimpPre.Qhi") (c "SimpPre.F") args))
                (env/update-extension :simp-lemmas #{} conj "SimpPre.q_hi"))
        st (tc/mk-tc-state env)
        goal (apply e/app* (c "SimpPre.Qhi") lam args)
        entries (si/lemma-keys ["SimpPre.q_hi"] env #(env/lookup env (name/from-string %)))
        [empty-post _] (simp/build-simp-indexes st env [])]
    (testing "eager index"
      (let [r (run env ["SimpPre.q_hi"] goal)]
        (is (= (c "True") (:expr r)))
        (is (checks? env goal r))))
    (doseq [[label trie] [["encoding 1" (si/build-simp-trie entries)]
                          ["encoding 2" (si/build-simp-trie (si/key-entries-artifact entries))]]]
      (testing label
        (let [r (simp/simp-expr-result st env empty-post goal 20 {:ext-trie trie})]
          (is (= (c "True") (:expr r)))
          (is (checks? env goal r)))))))

(def ^:private no-congr-fun-env
  ;; the bundled Init without congrFun (trust replay: what depends on it is admitted unchecked)
  (delay
    (parser/with-parser-state
      (parser/parse-ndjson-string @test-env/bundled-init-text)
      (fn [parsed]
        (:env (replay/replay (remove #(= "congrFun" (str (.name ^ansatz.kernel.ConstantInfo %))) (:decls parsed))
                             :verify? false :stop-on-error? true))))))

(deftest function-valued-ite-without-congrFun-selects-definitionally
  ;; the helper theorem is present but congrFun (for the extra argument) is not: the step must
  ;; not emit an undeclared constant; the instance is decided, so the selection is definitional
  (let [env (-> @no-congr-fun-env
                (ax "SimpPre.f1" (e/arrow nat nat)) (ax "SimpPre.g1" (e/arrow nat nat)) (ax "SimpPre.x1" nat))
        _ (is (nil? (env/lookup env (name/from-string "congrFun"))))
        nn (e/arrow nat nat)
        f-ite (e/app* (e/const' (name/from-string "ite") [(lvl/succ lvl/zero)]) nn (c "True")
                      (e/app* (c "Decidable.isTrue") (c "True") (c "True.intro"))
                      (c "SimpPre.f1") (c "SimpPre.g1"))
        goal (e/app f-ite (c "SimpPre.x1"))
        r (run env [] goal {})]
    (is (= (e/app (c "SimpPre.f1") (c "SimpPre.x1")) (:expr r)))
    (is (checks? env goal r))))

(deftest helper-free-ite-selection-needs-a-decidable-constructor
  ;; v4.36 Decidable is a structure, `Decidable.intro b r`; a constant of that name that is no
  ;; constructor of Decidable (here an opaque axiom, bundled Init predates 4.36) is stuck, so the
  ;; branch is not selected: the step would claim a false definitional equality
  (let [env (-> (pre-env)
                (ax "Decidable.intro" (e/forall' "p" prop (e/arrow (c "Bool") (e/arrow (e/bvar 1) (e/app (c "Decidable") (e/bvar 2))))
                                                 :implicit))
                (ax "SimpPre.u" nat))
        missing #{"ite_eq_left_of_eq_true" "ite_cond_eq_true"}
        inst (e/app* (c "Decidable.intro") (c "True") (c "Bool.true") (c "True.intro"))
        goal (e/app* (e/const' (name/from-string "ite") [(lvl/succ lvl/zero)]) nat (c "True") inst
                     (e/lit-nat 0) (c "SimpPre.u"))
        lookup env/lookup]
    (is (not (checks? env goal {:expr (e/lit-nat 0)})) "Eq.refl does not justify the selection")
    (with-redefs [env/lookup (fn [en n] (when-not (contains? missing (name/->string n)) (lookup en n)))]
      (let [r (run env [] goal {})]
        (is (not= (e/lit-nat 0) (:expr r)))
        (is (checks? env goal r))))))

(deftest eta-lookup-does-not-walk-a-discarded-argument
  ;; the query is keyed modulo eta node by node as the tree inspects it: a deep argument that
  ;; beta reduction discards is never traversed (it overflowed the stack when contracted whole)
  (let [env (-> (pre-env) (ax "SimpPre.D" (e/arrow nat nat)))
        xid 77001
        st (tc/attach-lctx (tc/mk-tc-state env) {xid {:tag :local :id xid :name "x" :type nat}})
        x (e/fvar xid)
        deep (loop [i 0 t x] (if (< i 200000) (recur (inc i) (e/app (c "SimpPre.D") t)) t))
        goal (e/app (e/lam "_" nat x :default) deep)
        [post pre] (simp/build-simp-indexes st env (simp/make-simp-lemmas env [{:name "SimpPre.pre_rule" :post false}]))
        r (simp/simp-expr-result st env post goal 20 {:pre-index pre})]
    (is (= x (:expr r)))))

(deftest a-lambda-keyed-pre-rule-is-judged-against-the-original-term
  ;; ↓ h : R (fun x => (fun z => z) (F x)) = R (fun x => F x) matches R (fun x => F x) only up to
  ;; beta; its rhs is the term itself, so it is no progress and simp terminates
  (let [nn (e/arrow nat nat)
        env (-> (pre-env)
                (ax "SimpPre.R" (e/arrow nn nat))
                (ax "SimpPre.h_lam" (eqn (e/app (c "SimpPre.R")
                                                (e/lam "x" nat (e/app (e/lam "z" nat (e/bvar 0) :default)
                                                                      (e/app (c "SimpPre.F") (e/bvar 0)))
                                                       :default))
                                         (e/app (c "SimpPre.R") (e/lam "x" nat (e/app (c "SimpPre.F") (e/bvar 0)) :default)))))
        goal (e/app (c "SimpPre.R") (e/lam "x" nat (e/app (c "SimpPre.F") (e/bvar 0)) :default))
        r (run env [{:name "SimpPre.h_lam" :post false}] goal)]
    (is (= goal (:expr r)))
    (is (checks? env goal r))))

(deftest eta-matching-under-an-enclosing-binder
  ;; h : Q (fun x => K (F x)) proves Q (fun x => K (fun y => F x y)): the structural matcher
  ;; rejects F x against fun y => F x y, the typed definitional match (eta) accepts it
  (let [nn (e/arrow nat nat)
        nnn (e/arrow nat nn)
        env (-> (pre-env)
                (ax "SimpPre.F2" nnn)
                (ax "SimpPre.K2" (e/arrow nn nat))
                (ax "SimpPre.Q2" (e/arrow nn prop))
                (ax "SimpPre.q2" (e/app (c "SimpPre.Q2")
                                        (e/lam "x" nat (e/app (c "SimpPre.K2") (e/app (c "SimpPre.F2") (e/bvar 0))) :default))))
        goal (e/app (c "SimpPre.Q2")
                    (e/lam "x" nat (e/app (c "SimpPre.K2")
                                          (e/lam "y" nat (e/app* (c "SimpPre.F2") (e/bvar 1) (e/bvar 0)) :default))
                           :default))
        r (run env ["SimpPre.q2"] goal)]
    (is (= (c "True") (:expr r)))
    (is (checks? env goal r))))

(deftest eta-lookup-without-an-environment-and-on-wide-applications
  ;; an environment-free lookup keeps a beta redex as `.other` (no eta to try); each argument's
  ;; alternatives are distinct, so 30 lambda arguments do not multiply the candidates
  (let [redex (e/app (e/lam "x" nat (e/bvar 0) :default) (e/lit-nat 0))
        rule {:lhs-pattern redex :name "SimpPre.redex"}
        lam (e/lam "x" nat (e/app (e/lam "_" nat (c "SimpPre.a") :default) (e/bvar 0)) :default)
        wide (apply e/app* (c "SimpPre.W") (repeat 30 lam))
        wide-rule {:lhs-pattern wide :name "SimpPre.wide"}]
    (is (= [rule] (dt/lookup-simp-tree (dt/make-simp-tree [rule]) redex)))
    (is (= [wide-rule] (dt/lookup-simp-tree (dt/make-simp-tree [wide-rule]) wide)))))

(deftest eta-matching-binds-a-rule-parameter
  ;; h : ∀ n, R (F n) = n on R (fun x => F a x): found through the eta spelling, matched by typed
  ;; unification with eta (Lean isDefEqEta), n := a
  (let [nn (e/arrow nat nat)
        env (-> (pre-env)
                (ax "SimpPre.F3" (e/arrow nat nn))
                (ax "SimpPre.R3" (e/arrow nn nat))
                (ax "SimpPre.h3" (e/forall' "n" nat (eqn (e/app (c "SimpPre.R3") (e/app (c "SimpPre.F3") (e/bvar 0)))
                                                         (e/bvar 0))
                                            :default)))
        goal (e/app (c "SimpPre.R3") (e/lam "x" nat (e/app* (c "SimpPre.F3") (c "SimpPre.a") (e/bvar 0)) :default))
        r (run env ["SimpPre.h3"] goal)]
    (is (= (c "SimpPre.a") (:expr r)))
    (is (checks? env goal r))))

(deftest equal-priority-eta-spellings-keep-their-insertion-order
  ;; test/lean-parity/simp/e_eta_equal_priority_order.lean: pre rules R L → 0, R F → s,
  ;; s → R L at one priority, L = fun x => F x. Lean keys R L and R F alike, so the argument
  ;; order decides: [rl rf sr] ends at 0, [rf rl sr] cycles R L → s → R L
  (let [nn (e/arrow nat nat)
        lam (e/lam "x" nat (e/app (c "SimpPre.F") (e/bvar 0)) :default)
        env (-> (pre-env)
                (ax "SimpPre.R4" (e/arrow nn nat)) (ax "SimpPre.s4" nat)
                (ax "SimpPre.rl" (eqn (e/app (c "SimpPre.R4") lam) (e/lit-nat 0)))
                (ax "SimpPre.rf" (eqn (e/app (c "SimpPre.R4") (c "SimpPre.F")) (c "SimpPre.s4")))
                (ax "SimpPre.sr" (eqn (c "SimpPre.s4") (e/app (c "SimpPre.R4") lam))))
        goal (e/app (c "SimpPre.R4") lam)
        r (run env [{:name "SimpPre.rl" :post false} {:name "SimpPre.rf" :post false}
                    {:name "SimpPre.sr" :post false}] goal)
        swapped (try (:expr (run env [{:name "SimpPre.rf" :post false} {:name "SimpPre.rl" :post false}
                                      {:name "SimpPre.sr" :post false}] goal))
                     (catch clojure.lang.ExceptionInfo _ ::loops))]
    (is (= (e/lit-nat 0) (:expr r)))
    (is (checks? env goal r))
    (is (not= (e/lit-nat 0) swapped) "rf first: no terminal 0")))

(deftest the-persistent-index-serves-only-registered-simp-rules
  ;; an index entry whose name the env does not register as a forward @[simp] rule (e.g. a
  ;; @[csimp] source keyed by an older importer) is never served
  (let [env (pre-env)
        st (tc/mk-tc-state env)
        trie (si/build-simp-trie (si/key-entries-artifact
                                  (si/lemma-keys ["SimpPre.post_rule"] env #(env/lookup env (name/from-string %)))))
        [post _] (simp/build-simp-indexes st env [])
        goal (e/app (c "SimpPre.F") (c "SimpPre.a"))]
    (is (= goal (:expr (simp/simp-expr-result st env post goal 20 {:ext-trie trie}))))
    (let [env (env/update-extension env :simp-lemmas #{} conj "SimpPre.post_rule")]
      (is (= (e/app (c "SimpPre.G") (c "SimpPre.a"))
             (:expr (simp/simp-expr-result st env post goal 20 {:ext-trie trie})))))))
