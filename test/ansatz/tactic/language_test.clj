(ns ansatz.tactic.language-test
  "Tactic language regressions; Lean pairs in test/lean/tactic_language.lean."
  (:require [clojure.test :refer [deftest is use-fixtures testing]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]))

(use-fixtures :once
  (fn [t]
    (let [saved @a/ansatz-env]
      (try (a/load-init!) (t) (finally (reset! a/ansatz-env saved))))))

(defn- proves [nm params stmt tactics]
  (binding [a/*verbose* false]
    (a/prove-theorem nm params stmt tactics)
    (is true)))

(deftest rewrite-hypothesis-location
  (proves 'rewrite_hypothesis_location
          '[x :- Nat, y :- Nat, h :- (= x y), hx :- (= x 1)]
          '(= y 1) '[(rw [h] at hx) (exact hx)]))

(deftest rewrite-multiple-hypotheses-and-target
  (proves 'rewrite_multiple_locations
          '[x :- Nat, y :- Nat, h :- (= x y), hx :- (= x 1), hx2 :- (= x 2)]
          '(And (= x 1) (= x 2))
          '[(rw [h] at hx hx2 ⊢) (constructor) (exact hx) (exact hx2)]))

(deftest rewrite-wildcard-skips-inapplicable-locations
  (proves 'rewrite_wildcard_locations
          '[x :- Nat, y :- Nat, h :- (= x y), hx :- (= x 1)]
          '(= y 1) '[(rw [h] at *) (exact hx)]))

(deftest rewrite-reversed-quantified-lemma-at-hypothesis
  (proves 'rewrite_reverse_local
          '[x :- Nat, y :- Nat, z :- Nat, hx :- (= (+ x (+ y z)) 1)]
          '(= (+ (+ x y) z) 1)
          '[(rw [← Nat.add_assoc] at hx) (exact hx)]))

(deftest rewrite-preserves-used-old-hypothesis
  (proves 'rewrite_dependent_local
          '[x :- Nat, y :- Nat, h :- (= x y), hx :- (= x 1), hh :- (= hx hx)]
          '(= y 1) '[(rw [h] at hx) (exact hx)]))

(deftest cases-substitutes-dependent-implications
  (proves 'cases_dependent_implications
          '[b :- Bool, x :- Bool, y :- Bool,
            ht :- (=> (= b true) (= x true)), hf :- (=> (= b false) (= y true))]
          '(= (if b x y) true) '[(cases b) (all_goals (simp_all))]))

(deftest cases-substitutes-transitive-dependents
  (proves 'cases_transitive_dependents
          '[b :- Bool, p :- (=> Bool Prop), h1 :- (p b),
            q :- (=> (p b) Prop), h2 :- (q h1)]
          '(q h1)
          '[(cases b)
            (have h1-special (p false) h1)
            (have h2-special (q h1-special) h2) (exact h2-special)
            (have h1-special (p true) h1)
            (have h2-special (q h1-special) h2) (exact h2-special)])
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Type mismatch"
                        (binding [a/*verbose* false]
                          (a/prove-theorem 'unspecialized_transitive_dependents
                                           '[b :- Bool, p :- (=> Bool Prop), h1 :- (p b),
                                             q :- (=> (p b) Prop), h2 :- (q h1)]
                                           '(q h1)
                                           '[(have h1-special (p false) h1)
                                             (have h2-special (q h1-special) h2)
                                             (exact h2-special)])))))

(deftest split-ifs-under-function-application
  (proves 'split_ifs_function
          '[b :- Bool, p :- (=> Nat Bool), n :- Nat]
          '(= (p (if b n n)) (p n)) '[(split_ifs) (all_goals (rfl))]))

(deftest split-ifs-repeats-nested-conditions
  (proves 'split_ifs_nested
          '[b :- Bool, c :- Bool, p :- (=> Nat Bool), n :- Nat]
          '(= (p (if b (if c n n) n)) (p n)) '[(split_ifs) (all_goals (rfl))]))

(deftest induction-named-alternatives
  (proves 'induction_named_alternatives '[n :- Nat] '(= (+ 0 n) n)
          '[(induction n :with [zero (rfl)]
                       [(succ k ih)
                        (change (= (Nat.succ (+ 0 k)) (Nat.succ k)))
                        (exact (congrArg Nat.succ ih))])]))

(deftest cases-named-alternatives
  (proves 'cases_named_alternatives '[p :- Prop, q :- Prop, h :- (Or p q)]
          '(Or q p)
          '[(cases h :with [(inl hp) (right) (exact hp)]
                   [(inr hq) (left) (exact hq)])]))

(deftest case-selects-tag-out-of-order
  (proves 'case_selects_tag '[p :- Prop, q :- Prop, h :- (Or p q)] '(Or q p)
          '[(cases h) (case (inr hq) (left) (exact hq))
            (case (inl hp) (right) (exact hp))]))

(deftest next-renames-branch-locals
  (proves 'next_renames_locals '[p :- Prop, q :- Prop, h :- (Or p q)] '(Or q p)
          '[(cases h) (next [hp] (right) (exact hp))
            (next [hq] (left) (exact hq))]))

(deftest combinator-failure-semantics
  (let [[ps _] (proof/start-proof (env/empty-env) (e/sort' lvl/zero))
        fail (fn [_] (throw (ex-info "not applicable" {:kind :tactic-error})))
        bug (fn [_] (throw (IllegalStateException. "bug")))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not applicable"
                          (basic/all-goals ps fail)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"failed on all goals"
                          (basic/any-goals ps fail)))
    (is (thrown-with-msg? IllegalStateException #"bug" (basic/any-goals ps bug)))
    (is (= ps (basic/all-goals ps identity)))))

(deftest any-goals-keeps-failed-goal-and-uses-applicable-goal
  (proves 'any_goals_partial '[p :- Prop, hp :- p] '(And True p)
          '[(constructor) (any_goals (exact hp)) (constructor)]))

(deftest unnamed-intros-are-inaccessible
  (let [[ps _] (proof/start-proof (env/empty-env)
                                  (e/forall' "p" (e/sort' lvl/zero) (e/bvar 0) :default))
        ps (a/run-tactic ps '(intro))
        decl (first (vals (:lctx (proof/current-goal ps))))]
    (is (re-find #"✝" (:name decl)))
    (is (:inaccessible decl))))

(deftest simp-all-rejects-locations
  (let [[ps _] (proof/start-proof (env/empty-env) (e/sort' lvl/zero))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"does not accept locations"
                          (a/run-tactic ps '(simp_all at *))))))

(deftest all-goals-isolates-and-preserves-goal-order
  (proves 'all_goals_order '[p :- Prop, q :- Prop, hp :- p, hq :- q]
          '(And (And p q) (And q p))
          '[(constructor) (all_goals (constructor))
            (exact hp) (exact hq) (exact hq) (exact hp)]))

(deftest and-then-leaves-existing-siblings-alone
  (proves 'and_then_siblings '[p :- Prop, q :- Prop, hp :- p, hq :- q]
          '(And (And p p) q)
          '[(constructor) (and_then (constructor) (exact hp)) (exact hq)]))

(deftest case-requires-complete-body
  (let [[ps _] (proof/start-proof (a/env)
                                  (e/const' (name/from-string "True") []))]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"did not close"
                          (a/run-tactic ps '(next))))))

(deftest alternatives-require-every-constructor
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"missing constructor alternatives"
                        (binding [a/*verbose* false]
                          (a/prove-theorem 'missing_alternative '[b :- Bool]
                                           '(= b b) '[(cases b :with [false (rfl)])])))))

(deftest list-induction-names-fields-and-induction-hypothesis
  (proves 'list_induction_names '[xs :- (List Nat)] '(= xs xs)
          '[(induction xs :with [nil (rfl)]
                       [(cons h t ih)
                        (change (= (List.cons Nat h t) (List.cons Nat h t)))
                        (exact (congrArg (fn [ys :- (List Nat)] (List.cons Nat h ys)) ih))])]))

(deftest list-cases-names-only-constructor-fields
  (proves 'list_cases_names '[xs :- (List Nat)] '(= xs xs)
          '[(cases xs :with [nil (rfl)]
                   [(cons h t)
                    (change (= (List.cons Nat h t) (List.cons Nat h t)))
                    (rfl)])]))

(deftest nested-cases-preserve-parent-tags
  (proves 'nested_case_tags '[b :- Bool, c :- Bool] '(= b b)
          '[(cases b) (cases c)
            (case false.true (rfl)) (case false.false (rfl))
            (case true (rfl))]))

(deftest underscore-intros-use-inaccessible-names
  (let [[ps _] (proof/start-proof (env/empty-env)
                                  (e/forall' "p" (e/sort' lvl/zero) (e/bvar 0) :default))
        ps (a/run-tactic ps '(intro _))
        decl (first (vals (:lctx (proof/current-goal ps))))]
    (is (re-find #"✝" (:name decl)))
    (is (:inaccessible decl))))

(deftest split-ifs-splits-conditions-inside-conditions-first
  (let [c (fn [s] (e/const' (name/from-string s) []))
        bool (c "Bool")
        nat (c "Nat")
        inner (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                      (e/lam "_" bool bool :default) (e/bvar 0) (e/bvar 1) (e/bvar 2))
        outer (e/app* (e/const' (name/from-string "Bool.rec") [(lvl/succ lvl/zero)])
                      (e/lam "_" bool nat :default) (e/lit-nat 1) (e/lit-nat 0) inner)
        target (e/app (e/bvar 3) outer)
        target (reduce #(e/forall' %2 bool %1 :default) target ["d" "c" "b"])
        target (e/forall' "p" (e/arrow nat (e/sort' lvl/zero)) target :default)
        [ps _] (proof/start-proof (a/env) target)
        ps (basic/intros ps ["p" "b" "c" "d"])
        b (e/fvar (second (sort (keys (:lctx (proof/current-goal ps))))))
        ps (basic/split-ifs ps)]
    (is (seq (:goals ps)))
    (doseq [gid (:goals ps)]
      (is (some (fn [[_ decl]]
                  (let [[hd args] (e/get-app-fn-args (:type decl))]
                    (and (e/const? hd) (= "Eq" (name/->string (e/const-name hd)))
                         (= 3 (count args)) (= b (second args)))))
                (proof/mvar-lctx ps gid))))))

(deftest indexed-cases-retains-used-original-major
  (a/inductive CaseShape [] :in Type (base) (node [prev CaseShape]))
  (a/inductive LocalEvidence [] :in Prop :indices [n CaseShape]
               (zero :where [CaseShape.base])
               (step [k CaseShape] :where [(CaseShape.node k)]))
  (proves 'indexed_cases_used_major
          '[n :- CaseShape, h :- (LocalEvidence (CaseShape.node n)), hh :- (= h h)]
          '(= n n) '[(cases h) (change (= k k)) (rfl)]))

(deftest split-ifs-retains-false-branches-for-later-contradiction
  (proves 'split_ifs_false_branch '[b :- Bool, hb :- (= b true)]
          '(= (if b 0 1) 0) '[(split_ifs) (all_goals (simp_all))]))

(deftest split-ifs-preserves-existing-sibling-goals
  (proves 'split_ifs_siblings '[b :- Bool]
          '(And (= (if b 0 1) (if b 0 1)) True)
          '[(constructor) (split_ifs) (constructor)]))

(deftest induction-partial-alternative-names-start-with-fields
  (proves 'partial_induction_names '[n :- Nat] '(= n n)
          '[(induction n :with [zero (rfl)]
                       [(succ k)
                        (change (= (Nat.succ k) (Nat.succ k))) (rfl)])]))

(deftest partial-alternative-names-exclude-inherited-inaccessibles
  (proves 'nested_partial_induction_names '[p :- Prop, hp :- p, n :- Nat]
          '(=> p (= n n))
          '[(intro) (induction n :with [zero (rfl)]
                               [(succ k)
                                (change (= (Nat.succ k) (Nat.succ k))) (rfl)])]))

(deftest partial-alternative-names-put-all-fields-before-ihs
  (a/inductive BranchOrder [] :in Type (leaf) (node [prev BranchOrder] [value Nat]))
  (proves 'partial_recursive_field_order '[x :- BranchOrder] '(= x x)
          '[(induction x :with [leaf (rfl)]
                       [(node child value)
                        (change (= (BranchOrder.node child value)
                                   (BranchOrder.node child value)))
                        (rfl)])]))

(deftest split-reduces-propositional-conditionals
  (doseq [tactic ['split 'split_ifs]]
    (proves (symbol (str "conditional_branches_" tactic))
            '[i :- Nat, j :- Nat, p :- (=> Nat Prop),
              ht :- (p 10), hf :- (p 20)]
            '(p (if (== i j) 10 20))
            [(list tactic) '(all_goals (assumption))])))

(deftest split-reduces-dependent-conditionals
  (doseq [tactic ['split 'split_ifs]]
    (proves (symbol (str "dependent_conditional_branches_" tactic))
            '[c :- Prop, dec :- (Decidable c), p :- (=> Nat Prop),
              t :- (=> c Nat), f :- (=> (Not c) Nat),
              ht :- (forall [h :- c] (p (t h))),
              hf :- (forall [h :- (Not c)] (p (f h)))]
            '(p (dite c t f))
            [(list tactic) '(all_goals (first (apply ht) (apply hf)))])))

(deftest rewrite-instantiates-universe-from-matched-conditional
  (proves 'rewrite_if_pos_universe
          '[i :- Nat, j :- Nat, h :- (= i j), p :- (=> Nat Prop), hp :- (p i)]
          '(p (if (== i j) i j))
          '[(rw [(if_pos h)]) (exact hp)])
  ;; The lemma's universe occurs only in the pending implicit branch arguments.
  (proves 'rewrite_if_neg_universe
          '[c :- Prop, dec :- (Decidable c), h :- (Not c),
            x :- Nat, y :- Nat, p :- (=> Nat Prop), hp :- (p y)]
          '(p (ite c x y))
          '[(rw [(if_neg h)]) (exact hp)]))

(deftest apply-placeholder-unifies-with-local
  (proves 'applied_placeholder
          '[i :- Nat, j :- Nat, n :- Nat,
            p :- (=> Nat Nat Nat Prop),
            lemma :- (forall [x :- Nat y :- Nat z :- Nat] (p x y z))]
          '(p i j n) '[(apply (lemma _ j n))]))

(deftest assumption-assigns-shared-metavariables
  (proves 'assumption_shared_hole
          '[p :- (=> Nat Prop), q :- (=> Nat Prop), n :- Nat,
            hp :- (p n), hq :- (q n),
            irrelevant :- True,
            lemma :- (forall [x :- Nat] (=> (p x) (=> (q x) True)))]
          'True
          '[(apply (lemma _)) (assumption) (assumption)]))

(deftest rename-inaccessible-indexed-fields
  (a/inductive RenameShape [] :in Type (base) (node [prev RenameShape]))
  (a/inductive ScopedEvidence [] :in Prop :indices [n RenameShape]
               (base :where [RenameShape.base])
               (mk [n RenameShape] [hi (Eq RenameShape n n)] :where [(RenameShape.node n)]))
  (proves 'rename_indexed_fields
          '[n :- RenameShape, h :- (ScopedEvidence (RenameShape.node n))]
          '(= n n) '[(cases h) (rename_i hi) (exact hi)]))

(deftest induction-generalizing-reverts-later-dependents
  (proves 'induction_generalizing_dependents
          '[n :- Nat, m :- Nat, h :- (= m n), hh :- (= h h)]
          '(= (+ 0 m) n)
          '[(induction n generalizing m)
            (all_goals (rw [h])) (all_goals (simp [Nat.zero_add]))]))

(deftest split-keeps-reduced-branches-and-sibling-goals-open
  (proves 'split_open_branches
          '[i :- Nat, j :- Nat, x :- Nat, y :- Nat]
          '(And (= (if (== i j) x y) (if (== i j) x y)) True)
          '[(constructor) (split) (rfl) (rfl) (constructor)]))

(deftest rename-inaccessible-selects-trailing-fields
  (proves 'rename_trailing_fields
          '[p :- Prop, q :- Prop, h :- (And p q)] 'q
          '[(cases h) (rename_i hq) (exact hq)])
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"too many"
                       (binding [a/*verbose* false]
                         (a/prove-theorem 'rename_too_many '[p :- Prop] '(=> p p)
                                          '[(intro) (rename_i x y) (exact y)])))))

(deftest induction-on-indexed-proof-generalizes-later-locals
  (a/inductive CountEvidence [] :in Prop :indices [n Nat]
               (zero :where [0])
               (step [n Nat] [h (CountEvidence n)] :where [(Nat.succ n)]))
  (proves 'indexed_induction_generalizing
          '[n :- Nat, h :- (CountEvidence n), m :- Nat, hm :- (= m n), hh :- (= hm hm)]
          '(= (+ 0 m) n)
          '[(induction h generalizing m)
            (all_goals (rw [hm])) (all_goals (simp [Nat.zero_add]))]))

(deftest split-ifs-under-binders-with-closed-condition
  (proves 'conditional_under_binder
          '[c :- Prop, dec :- (Decidable c), p :- (=> Nat Nat Prop),
            ht :- (forall [n :- Nat] (p n n)), hf :- (forall [n :- Nat] (p n 0))]
          '(forall [n :- Nat] (p n (ite c n 0)))
          '[(split_ifs) (all_goals (intro n) (first (apply ht) (apply hf)))]))

(deftest rewrite-sequence-allocates-fresh-lemma-parameters
  (proves 'rewrite_sequence_fresh_parameters
          '[f :- (=> Nat Nat), g :- (=> Nat Nat), k :- (=> Nat Nat),
            h :- (=> Nat Nat), p :- (=> Nat Prop), n :- Nat,
            first-rule :- (forall [x :- Nat] (= (f x) (g (k x)))),
            second-rule :- (forall [y :- Nat] (= (g y) (h y))),
            third-rule :- (forall [z :- Nat] (= (h z) z)), hp :- (p (k n))]
          '(p (f n))
          '[(rw [first-rule second-rule third-rule]) (exact hp)]))
