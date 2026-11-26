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
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.basic :as basic]
            [ansatz.simp-index :as si]))

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
  (let [env (pre-env)
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
