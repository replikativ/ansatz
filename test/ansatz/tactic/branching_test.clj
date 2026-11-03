(ns ansatz.tactic.branching-test
  "Rewrite obligations and located splits; pairs in test/lean/branching.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.meta :as meta]
            [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.instance :as inst]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.proof :as proof]))

(use-fixtures :once
  (fn [t]
    (let [saved @a/ansatz-env]
      (try (a/load-init!) (t) (finally (reset! a/ansatz-env saved))))))

(defn- proves [nm params stmt tactics]
  (binding [a/*verbose* false]
    (a/prove-theorem nm params stmt tactics)
    (is true)))

(deftest rewrite-exposes-explicit-proof-hole
  (proves 'rewrite_explicit_obligation
          '[n :- Nat, rule :- (forall [x :- Nat, h :- True] (= (+ x 0) x))]
          '(= (+ n 0) n) '[(rw [(rule _ _)]) (exact True.intro)]))

(deftest rewrite-exposes-telescope-proof-hole
  (proves 'rewrite_telescope_obligation
          '[n :- Nat, rule :- (forall [x :- Nat, h :- True] (= (+ x 0) x))]
          '(= (+ n 0) n) '[(rw [rule]) (exact True.intro)]))

(deftest rewrite-obligations-follow-target-and-precede-siblings
  (proves 'rewrite_obligation_order
          '[n :- Nat, p :- Prop, hp :- p,
            rule :- (forall [x :- Nat, h :- True] (= (+ x 0) x))]
          '(And (= (+ n 0) n) p)
          '[(constructor) (rewrite (rule _ _)) (rfl) (exact True.intro) (exact hp)]))

(deftest rewrite-reverse-at-local-retains-proof-obligation
  (proves 'rewrite_reverse_local_obligation
          '[n :- Nat, rule :- (forall [x :- Nat, h :- True] (= (+ x 0) x)), hx :- (= n 1)]
          '(= (+ n 0) 1)
          '[(rewrite ← (rule n _) at hx) (exact hx) (exact True.intro)]))

(deftest rewrite-data-hole-remains-a-goal
  (proves 'rewrite_inferred_data_obligation
          '[n :- Nat,
            rule :- (forall [x :- Nat, y :- Nat, h :- (= y 0)] (= (+ x 0) x))]
          '(= (+ n 0) n) '[(rw [(rule _ _ _)]) (exact 0) (rfl)]))

(deftest proposition-by-cases-names-positive-and-negative-branches
  (proves 'named_prop_cases '[p :- Prop] '(Or p (Not p))
          '[(by_cases hp :- p) (case pos (left) (exact hp))
            (case neg (right) (exact hp))]))

(deftest proposition-by-cases-preserves-siblings
  (proves 'prop_cases_siblings '[p :- Prop, q :- Prop, hq :- q]
          '(And (Or p (Not p)) q)
          '[(constructor) (by_cases hp :- p)
            (left) (exact hp) (right) (exact hp) (exact hq)]))

(deftest proposition-by-cases-uses-local-decidable
  (let [ty (elab/elaborate (a/env) '(forall [p :- Prop, d :- (Decidable p)] (Or p (Not p))))
        [ps _] (proof/start-proof (a/env) ty)
        ps (basic/intros ps ["p" "d"])
        g (proof/current-goal ps)
        d (first (for [[id decl] (:lctx g) :when (= "d" (:name decl))] id))
        ps (a/run-tactic ps '(by_cases hp :- p))
        [head args] (e/get-app-fn-args (meta/expr-assignment (:meta-mctx ps) (:id g)))]
    (is (= "Decidable.casesOn" (name/->string (e/const-name head))))
    (is (= (e/fvar d) (nth args 2)))
    (let [ps (reduce a/run-tactic ps '[(left) (exact hp) (right) (exact hp)])
          term (extract/verify ps)]
      (is (not (.contains (e/->string term) "Classical.propDecidable"))))))

(deftest proposition-by-cases-default-name
  (proves 'default_prop_cases '[p :- Prop] '(Or p (Not p))
          '[(by_cases p) (left) (exact h) (right) (exact h)]))

(deftest boolean-by-cases-retains-order-and-supports-name
  (proves 'named_bool_cases '[b :- Bool] '(Or (= b false) (= b true))
          '[(by_cases hb :- b) (left) (exact hb) (right) (exact hb)]))

(deftest split-at-boolean-hypothesis
  (proves 'split_bool_local '[b :- Bool, h :- (= (if b 0 1) 0)] '(= b true)
          '[(split at h) (cases h) (exact hc)]))

(deftest split-at-decidable-hypothesis-keeps-branches-open
  (proves 'split_decidable_local
          (into '[p :- Prop, d :- (Decidable p)]
                ['hh ':- (list '= (list (symbol "@ite") 'Nat 'p 'd 0 1) 0)])
          'p '[(split at hh) (exact h) (cases hh)]))

(deftest split-at-local-preserves-dependent-hypothesis
  (proves 'split_bool_local_dependent
          '[b :- Bool, h :- (= (if b 0 1) 0), hh :- (= h h)]
          '(And (= b true) (= h h))
          '[(split at h) (cases h) (constructor) (exact hc) (exact hh)]))

(deftest split-at-wildcard-skips-unsplittable-hypothesis
  (proves 'split_wildcard_local '[b :- Bool, unused :- True, h :- (= (if b 0 1) 0)]
          '(= b true) '[(split at *) (cases h) (exact hc)]))

(deftest split-at-local-matcher-reintroduces-hypothesis-and-dependents
  (let [c (fn [s levels] (e/const' (name/from-string s) levels))
        bool (c "Bool" [])
        nat (c "Nat" [])
        l1 (lvl/succ lvl/zero)
        matcher (e/app* (c "List.filter.match_1" [l1])
                        (e/lam "_" bool nat :default) (e/bvar 0)
                        (e/lam "_" (c "Unit" []) (e/lit-nat 0) :default)
                        (e/lam "_" (c "Unit" []) (e/lit-nat 1) :default))
        hyp (e/app* (c "Eq" [l1]) nat matcher (e/lit-nat 0))
        goal (e/forall' "b" bool
                        (e/forall' "h" hyp
                                   (e/app* (c "Eq" [l1]) bool (e/bvar 1) (c "Bool.true" []))
                                   :default) :default)
        dep-type (e/app* (c "Eq" [lvl/zero]) (e/lift hyp 1 0) (e/bvar 0) (e/bvar 0))
        dep-goal (e/forall' "b" bool
                            (e/forall' "h" hyp
                                       (e/forall' "hh" dep-type
                                                  (e/app* (c "And" [])
                                                          (e/app* (c "Eq" [l1]) bool (e/bvar 2) (c "Bool.true" []))
                                                          (e/lift dep-type 1 0))
                                                  :default) :default) :default)]
    (proves 'split_match_local '[b h] goal '[(split at h) (rfl) (cases h)])
    (proves 'split_match_local_dependent '[b h hh] dep-goal
            '[(split at h) (constructor) (rfl) (exact hh) (cases h)])))

(deftest split-rejects-unknown-or-multiple-locations
  (let [[ps _] (proof/start-proof (a/env) (elab/elaborate (a/env) 'True))]
    (doseq [form '[(split at missing) (split at h h2) (split h)]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Tactic error: split:"
                            (a/run-tactic ps form))))))

(deftest rewrite-proof-goals-are-opaque
  (let [ty (elab/elaborate (a/env)
                           '(forall [n :- Nat,
                                     rule :- (forall [x :- Nat, h :- True] (= (+ x 0) x))]
                                    (= (+ n 0) n)))
        [ps _] (proof/start-proof (a/env) ty)
        ps (-> ps (basic/intros ["n" "rule"]) (a/run-tactic '(rewrite (rule _ _))))
        hole (second (:goals ps))]
    (is (= 2 (count (:goals ps))))
    (is (= :syntheticOpaque (:kind (proof/mvar-decl ps hole))))
    (is (= "True" (e/->string (proof/mvar-type ps hole))))
    (is (some? (extract/verify (-> ps (a/run-tactic '(rfl))
                                   (a/run-tactic '(exact True.intro))))))))

(deftest rewrite-preserves-preexisting-goals-and-their-kind
  (let [ty (elab/elaborate (a/env)
                           '(forall [n :- Nat,
                                     rule :- (forall [x :- Nat, h :- True] (= (+ x 0) x))]
                                    (= (+ n 0) n)))
        [ps _] (proof/start-proof (a/env) ty)
        ps (basic/intros ps ["n" "rule"])
        g (proof/current-goal ps)
        [[n _] [rule _]] (sort-by key (:lctx g))
        [ps old] (proof/fresh-mvar ps (elab/elaborate (a/env) 'True) (:lctx g) {:kind :natural})
        ps (basic/rewrite-lemma ps (e/app* (e/fvar rule) (e/fvar n) (e/mvar old)))]
    (is (= 2 (count (:goals ps))))
    (is (= old (second (:goals ps))))
    (is (= :natural (:kind (proof/mvar-decl ps old))))
    (is (some? (extract/verify (-> ps (a/run-tactic '(rfl))
                                   (a/run-tactic '(exact True.intro))))))))

(deftest rewrite-data-hole-is-assignable-from-proof-obligation
  (let [ty (elab/elaborate (a/env)
                           '(forall [n :- Nat,
                                     rule :- (forall [x :- Nat, y :- Nat, h :- (= y 0)] (= (+ x 0) x))]
                                    (= (+ n 0) n)))
        [ps _] (proof/start-proof (a/env) ty)
        ps (-> ps (basic/intros ["n" "rule"]) (a/run-tactic '(rw [(rule _ _ _)])))
        [data-id proof-id] (:goals ps)]
    (is (= 2 (count (:goals ps))))
    (is (= :syntheticOpaque (:kind (proof/mvar-decl ps proof-id))))
    (is (not= :syntheticOpaque (:kind (proof/mvar-decl ps data-id))))
    (let [ps (-> (assoc ps :goals [proof-id data-id]) (a/run-tactic '(rfl)))]
      (is (proof/solved? ps))
      (is (some? (extract/verify ps))))))

(deftest split-explicit-target-and-wildcard-fallback
  (doseq [tactic '[(split at ⊢) (split at *)]]
    (let [ty (elab/elaborate (a/env) '(forall [b :- Bool, n :- Nat, unused :- True] (= (if b n n) n)))
          [ps _] (proof/start-proof (a/env) ty)
          ps (basic/intros ps ["b" "n" "unused"])
          old (proof/current-goal ps)
          b (first (for [[id d] (:lctx old) :when (= "b" (:name d))] id))
          ps (a/run-tactic ps tactic)]
      (is (= 2 (count (:goals ps))))
      (is (= ["Bool.false" "Bool.true"]
             (mapv (fn [g]
                     (let [decl (first (for [[id d] (:lctx g)
                                             :when (and (= "hc" (:name d)) (not (contains? (:lctx old) id)))] d))
                           [_ args] (e/get-app-fn-args (:type decl))]
                       (is (= (e/fvar b) (nth args 1)))
                       (e/->string (nth args 2)))) (proof/goals ps))))
      (is (every? #(not= (:type old) (:type %)) (proof/goals ps)))
      (is (some? (extract/verify (a/run-tactic ps '(all_goals (rfl)))))))))

(defn- context-closed? [goal]
  (let [close #(reduce e/abstract1 % (keys (:lctx goal)))]
    (every? #(not (e/has-fvar-flag (close %)))
            (cons (:type goal) (mapcat (fn [[_ d]] (remove nil? [(:type d) (:value d)])) (:lctx goal))))))

(deftest split-decidable-local-preserves-target-and-context-dependencies
  (let [hyp (list '= (list (symbol "@ite") 'Nat 'p 'd 0 1) 0)
        params (into '[p :- Prop, d :- (Decidable p)] ['hh ':- hyp 'dep ':- '(= hh hh)])
        ty (elab/elaborate (a/env) (list 'forall params '(= hh hh)))
        [ps _] (proof/start-proof (a/env) ty)
        ps (basic/intros ps ["p" "d" "hh" "dep"])
        old (proof/current-goal ps)
        hh (first (for [[id d] (:lctx old) :when (= "hh" (:name d))] id))
        dep (first (for [[id d] (:lctx old) :when (= "dep" (:name d))] id))
        ps (a/run-tactic ps '(split at hh))]
    (is (= 2 (count (:goals ps))))
    (doseq [g (proof/goals ps)]
      (is (context-closed? g))
      (is (= (:type old) (:type g)))
      (is (= (get-in old [:lctx dep]) (get-in g [:lctx dep])))
      (is (contains? (:lctx g) hh))
      (is (= 2 (count (filter #(= "hh" (:name %)) (vals (:lctx g)))))))
    (is (some? (extract/verify (a/run-tactic ps '(all_goals (rfl))))))))

(deftest split-decidable-local-retains-named-true-replacement
  (let [hyp (list (symbol "@ite") 'Prop 'p 'd 'True 'True)
        params (into '[p :- Prop, d :- (Decidable p)] ['hh ':- hyp])
        ty (elab/elaborate (a/env) (list 'forall params 'True))
        [ps _] (proof/start-proof (a/env) ty)
        ps (-> ps (basic/intros ["p" "d" "hh"]) (a/run-tactic '(split at hh)))]
    (is (= 2 (count (:goals ps))))
    (doseq [g (proof/goals ps)]
      (is (context-closed? g))
      (is (= ["True"] (mapv (comp e/->string :type) (filter #(= "hh" (:name %)) (vals (:lctx g)))))))
    (is (some? (extract/verify (a/run-tactic ps '(all_goals (exact hh))))))))

(deftest rewrite-synthesizes-instance-implicit-parameters
  (let [eqn (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                    (e/const' (name/from-string "Nat") [])
                    (e/app* (e/const' (name/from-string "Nat.add") []) (e/lit-nat 1) (e/lit-nat 0))
                    (e/lit-nat 1))
        inst-type (elab/elaborate (a/env) '(Inhabited Nat))
        rule-type (e/forall' "inst" inst-type eqn :inst-implicit)
        ty (e/forall' "rule" rule-type eqn :default)
        [ps _] (proof/start-proof (a/env) ty)
        ps (-> ps (basic/intro "rule") (a/run-tactic '(rewrite rule)))]
    (is (= 1 (count (:goals ps))))
    (is (= "(Eq.{1} Nat 1 1)" (e/->string (:type (proof/current-goal ps)))))
    (is (some? (extract/verify (a/run-tactic ps '(rfl)))))))

(deftest rewrite-reports-unsynthesizable-instance
  (let [eqn (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                    (e/const' (name/from-string "Nat") [])
                    (e/app* (e/const' (name/from-string "Nat.add") []) (e/lit-nat 1) (e/lit-nat 0))
                    (e/lit-nat 1))
        rule-type (e/forall' "inst" (elab/elaborate (a/env) '(Inhabited False)) eqn :inst-implicit)
        [ps _] (proof/start-proof (a/env) (e/forall' "rule" rule-type eqn :default))
        ps (basic/intro ps "rule")]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Tactic error: rewrite: failed to synthesize"
                          (a/run-tactic ps '(rewrite rule))))))

(deftest try-clear-keeps-dependencies-then-clears-independent-local
  (let [ty (elab/elaborate (a/env) '(forall [n :- Nat, dep :- (= n n), unused :- True] (= n n)))
        [ps _] (proof/start-proof (a/env) ty)
        ps (basic/intros ps ["n" "dep" "unused"])
        ids (into {} (map (fn [[id d]] [(:name d) id]) (:lctx (proof/current-goal ps))))
        kept (basic/try-clear ps (ids "n"))
        cleared (basic/try-clear kept (ids "unused"))]
    (is (= ps kept))
    (is (not (contains? (:lctx (proof/current-goal cleared)) (ids "unused"))))
    (is (some? (extract/verify (a/run-tactic cleared '(rfl)))))
    (with-redefs [basic/clear (fn [& _] (throw (IllegalStateException. "clear bug")))]
      (is (thrown-with-msg? IllegalStateException #"clear bug" (basic/try-clear ps (ids "unused")))))))

(deftest simp-local-false-closes-after-clearing-original
  (proves 'simp_local_false_closes '[hh :- (And True False)] 'False '[(simp at hh)]))

(defn- out-param-rewrite-proof []
  (let [c #(e/const' (name/from-string %) [])
        nat (c "Nat")
        eqn (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                    nat (e/app* (c "Nat.add") (e/lit-nat 1) (e/lit-nat 0)) (e/lit-nat 1))
        hadd (e/app* (e/const' (name/from-string "HAdd") [lvl/zero lvl/zero lvl/zero])
                     nat nat (e/bvar 0))
        rule (e/forall' "alpha" (e/sort' (lvl/succ lvl/zero))
                        (e/forall' "inst" hadd eqn :inst-implicit) :implicit)
        [ps _] (proof/start-proof (a/env) (e/forall' "rule" rule eqn :default))]
    (basic/intro ps "rule")))

(deftest rewrite-synthesis-assigns-output-parameters
  (let [ps (out-param-rewrite-proof)
        rewritten (a/run-tactic ps '(rewrite rule))
        alpha (first (for [[id d] (get-in rewritten [:meta-mctx :decls])
                           :when (= "alpha" (some-> (:user-name d) name/->string))] id))]
    (is (= 1 (count (:goals rewritten))))
    (is (= (e/const' (name/from-string "Nat") [])
           (meta/zonk-expr (:meta-mctx rewritten) (e/mvar alpha))))
    (is (some? (extract/verify (a/run-tactic rewritten '(rfl)))))
    (let [closed (a/run-tactic ps '(rw [rule]))]
      (is (proof/solved? closed))
      (is (some? (extract/verify closed))))))

(deftest apply-synthesis-retains-output-parameter-assignments
  (let [ps (a/run-tactic (out-param-rewrite-proof) '(apply rule))]
    (is (proof/solved? ps))
    (is (some? (extract/verify ps)))))

(deftest instance-search-skips-inapplicable-rule-before-applicable-rule
  (let [nat (e/const' (name/from-string "Nat") [])
        truth (e/const' (name/from-string "True") [])
        falsehood (e/const' (name/from-string "False") [])
        inhabited #(e/app (e/const' (name/from-string "Inhabited") [%1]) %2)
        eqn (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)])
                    nat (e/app* (e/const' (name/from-string "Nat.add") []) (e/lit-nat 1) (e/lit-nat 0)) (e/lit-nat 1))]
    (doseq [[goal tactic] [[truth '(first (apply bad) (apply good))]
                           [eqn '(first (rw [bad]) (rw [good]))]]]
      (let [bad (e/forall' "inst" (inhabited lvl/zero falsehood) goal :inst-implicit)
            good (e/forall' "inst" (inhabited (lvl/succ lvl/zero) nat) goal :inst-implicit)
            ty (e/forall' "bad" bad (e/forall' "good" good goal :default) :default)
            [ps _] (proof/start-proof (a/env) ty)
            ps (a/run-tactic (basic/intros ps ["bad" "good"]) tactic)]
        (is (proof/solved? ps))
        (is (some? (extract/verify ps)))))))

(deftest synthesis-programming-errors-propagate
  (with-redefs [inst/synth-instance (fn [& _] (throw (IllegalStateException. "synthesis bug")))]
    (doseq [tactic '[(apply rule) (rewrite rule)]]
      (is (thrown-with-msg? IllegalStateException #"synthesis bug"
                            (a/run-tactic (out-param-rewrite-proof) tactic))))))

(deftest synthesized-instance-must-unify-with-its-full-type
  (with-redefs [inst/synth-instance (fn [mctx & _]
                                      [mctx (e/const' (name/from-string "Bool.true") [])])]
    (doseq [tactic '[(apply rule) (rewrite rule)]]
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"failed to assign synthesized instance"
                            (a/run-tactic (out-param-rewrite-proof) tactic))))))

(deftest split-decidable-local-is-positive-first
  (let [hyp (list '= (list (symbol "@ite") 'Nat 'p 'd 0 1) 0)
        params (into '[p :- Prop, d :- (Decidable p)] ['hh ':- hyp])
        ty (elab/elaborate (a/env) (list 'forall params 'p))
        [ps _] (proof/start-proof (a/env) ty)
        ps (basic/intros ps ["p" "d" "hh"])
        pid (first (for [[id d] (:lctx (proof/current-goal ps)) :when (= "p" (:name d))] id))
        ps (a/run-tactic ps '(split at hh))]
    (is (= [(e/fvar pid) (e/app (e/const' (name/from-string "Not") []) (e/fvar pid))]
           (mapv (fn [g] (:type (first (filter #(= "h" (:name %)) (vals (:lctx g)))))) (proof/goals ps))))
    (is (some? (extract/verify (reduce a/run-tactic ps '[(exact h) (cases hh)]))))))

(deftest wildcard-split-skips-local-used-by-target
  (let [ite #(list (symbol "@ite") 'Prop %1 %2 'True 'True)
        params (into '[p :- Prop, q :- Prop, dp :- (Decidable p), dq :- (Decidable q)]
                     ['hh ':- (ite 'p 'dp) 'other ':- (ite 'q 'dq)])
        ty (elab/elaborate (a/env) (list 'forall params '(= hh hh)))
        [ps _] (proof/start-proof (a/env) ty)
        ps (basic/intros ps ["p" "q" "dp" "dq" "hh" "other"])
        before (proof/current-goal ps)
        locals (into {} (map (fn [[id d]] [(:name d) id]) (:lctx before)))
        ps (a/run-tactic ps '(split at *))]
    (is (= 2 (count (:goals ps))))
    (is (= [(e/fvar (locals "q"))
            (e/app (e/const' (name/from-string "Not") []) (e/fvar (locals "q")))]
           (mapv (fn [g] (:type (first (filter #(= "h" (:name %)) (vals (:lctx g)))))) (proof/goals ps))))
    (doseq [g (proof/goals ps)]
      (is (context-closed? g))
      (is (= (:type before) (:type g)))
      (is (= [(get-in before [:lctx (locals "hh")])]
             (vec (filter #(= "hh" (:name %)) (vals (:lctx g))))))
      (is (= ["True"] (mapv (comp e/->string :type)
                            (filter #(= "other" (:name %)) (vals (:lctx g)))))))
    (is (some? (extract/verify (a/run-tactic ps '(all_goals (rfl))))))))

(deftest apply-constrains-instance-output-type-before-synthesis
  (let [c #(e/const' (name/from-string %) [])
        hadd #(e/app* (e/const' (name/from-string "HAdd") [lvl/zero lvl/zero lvl/zero])
                      (c "Nat") (c "Nat") %)
        rule (e/forall' "alpha" (e/sort' (lvl/succ lvl/zero))
                        (e/forall' "inst" (hadd (e/bvar 0))
                                   (e/forall' "x" (e/bvar 1) (e/bvar 2) :default)
                                   :inst-implicit) :implicit)
        ty (e/forall' "boolAdd" (hadd (c "Bool"))
                      (e/forall' "rule" rule (c "Nat") :default) :inst-implicit)
        [ps _] (proof/start-proof (a/env) ty)
        ps (basic/intros ps ["boolAdd" "rule"])
        ex (try (a/run-tactic ps '(apply rule)) nil
                (catch clojure.lang.ExceptionInfo ex
                  (if (= :tactic-error (:kind (ex-data ex))) ex (throw ex))))]
    ;; Lean rejects the conflicting local out-param instance after constraining alpha.
    (is (some? ex))
    (is (re-find #"failed to synthesize instance" (or (some-> ex .getMessage) "")))
    (is (= (hadd (c "Nat")) (:type (ex-data ex))))
    (is (some? (extract/verify (basic/exact ps (e/lit-nat 0)))))))
