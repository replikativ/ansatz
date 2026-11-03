(ns ansatz.tactic.branching-test
  "Rewrite obligations and located splits; pairs in test/lean/branching.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.basic :as basic]
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
  (proves 'local_decidable_cases '[p :- Prop, d :- (Decidable p)] '(Or p (Not p))
          '[(by_cases hp :- p) (left) (exact hp) (right) (exact hp)]))

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
          'p '[(split at hh) (cases hh) (exact h)]))

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
  (doseq [[nm tactic] [['split_explicit_target '(split at ⊢)]
                       ['split_wildcard_target '(split at *)]]]
    (proves nm '[b :- Bool, n :- Nat, unused :- True] '(= (if b n n) n)
            [tactic '(all_goals (rfl))])))
