(ns ansatz.tactic.small-forms-test
  "Lean v4.33.1 pairs: test/lean/small_forms.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.name :as name]
            [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.proof :as proof]))

(use-fixtures :once
  (fn [f]
    (let [saved @a/ansatz-env]
      (try (binding [a/*verbose* false] (a/load-init!) (f))
           (finally (reset! a/ansatz-env saved))))))

(defn- proves [nm params target tactics]
  (a/prove-theorem nm params target tactics)
  (is true))

(deftest trace-state-prints-goals-without-changing-state
  (let [[ps _] (proof/start-proof (a/env)
                                  (elab/elaborate (a/env) '(forall [n :- Nat] (And True True))))
        ps (-> ps (a/run-tactic '(intro n)) (a/run-tactic '(constructor)))
        result (atom nil)
        output (with-out-str (reset! result (a/run-tactic ps '(trace_state))))]
    (is (identical? ps @result))
    (is (re-find #"2 goal\(s\)" output))
    (is (= 2 (count (re-seq #"n : Nat" output))))
    (is (= 2 (count (re-seq #"⊢ True" output))))
    (let [done (a/run-tactic ps '(all_goals (exact True.intro)))]
      (is (= "No goals\n" (with-out-str (is (= done (a/run-tactic done '(trace_state)))))))))
  (is (re-find #"⊢ True"
               (with-out-str
                 (proves 'trace_then_exact '[] 'True '[(trace_state) (exact True.intro)])))))

(deftest case-prime-keeps-an-open-body-and-tag
  ;; The reporter's empty case body must leave the selected branch available.
  (proves 'case_prime_open '[n :- Nat] '(= n n)
          '[(cases n) (case' zero) (case zero (rfl)) (case succ (rfl))])
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"did not close"
                        (a/prove-theorem 'strict_case_open '[n :- Nat] '(= n n)
                                         '[(cases n) (case zero)])))
  ;; One fresh residual inherits the selected tag, even after a goal-producing tactic.
  (proves 'case_prime_restores_tag '[b :- Bool] '(And True True)
          '[(cases b) (case' true (constructor) (exact True.intro))
            (case true (exact True.intro))
            (case false (constructor) (all_goals (exact True.intro)))])
  (proves 'case_prime_closes_selected '[b :- Bool] '(= b b)
          '[(cases b) (case' true (rfl)) (case false (rfl))])
  (proves 'case_prime_renames_field '[p :- Prop, q :- Prop, h :- (Or p q)] '(Or q p)
          '[(cases h) (case' (inr hq) (left)) (case inr (exact hq))
            (case (inl hp) (right) (exact hp))]))

(deftest case-prime-keeps-multiple-residual-tags-and-siblings
  (let [[ps _] (proof/start-proof (a/env)
                                  (elab/elaborate (a/env) '(forall [b :- Bool] (And True True))))
        ps (-> ps (a/run-tactic '(intro b)) (a/run-tactic '(cases b)))
        sibling (first (:goals ps))
        sibling-view (first (proof/goals ps))
        selected (a/run-tactic ps '(case' true (constructor)))
        tags (mapv #(name/->string (:user-name %)) (proof/goals selected))]
    (is (= 3 (count (:goals selected))))
    (is (= sibling (last (:goals selected))))
    (is (= sibling-view (last (proof/goals selected))))
    (is (= 2 (count (distinct (take 2 tags)))))
    (is (every? #(.startsWith ^String % "true.") (take 2 tags)))
    (is (proof/solved? (-> selected
                           (a/run-tactic '(all_goals (constructor)))
                           (a/run-tactic '(all_goals (exact True.intro)))))))
  (proves 'case_prime_splits '[b :- Bool] '(And True True)
          '[(cases b) (case' true (constructor))
            (all_goals (first (exact True.intro) (constructor)))
            (all_goals (exact True.intro))]))

(deftest exact-uses-definitional-right-zero
  ;; Lean Elab/Tactic/ElabTerm.lean evalExact checks definitional equality.
  (doseq [[nm term] [['exact_surface_right_zero '(+ j 0)]
                     ['exact_explicit_right_zero '(Nat.add j 0)]
                     ['exact_constructor_right_zero '(Nat.add j Nat.zero)]]]
    (proves nm ['j ':- 'Nat 'P ':- '(=> Nat Prop) 'h ':- (list 'P term)]
            '(P j) '[(exact h)]))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Type mismatch"
                        (a/prove-theorem 'exact_left_zero
                                         '[j :- Nat, P :- (=> Nat Prop), h :- (P (+ 0 j))]
                                         '(P j) '[(exact h)])))
  (proves 'exact_nested_right_zero
          '[j :- Nat, subst :- (=> Nat Nat Nat Nat), v :- Nat, x :- Nat,
            P :- (=> Nat Prop), h :- (P (subst (+ j 0) v x))]
          '(P (subst j v x)) '[(exact h)])
  (proves 'exact_applied_right_zero
          '[j :- Nat, subst :- (=> Nat Nat Nat Nat), v :- Nat, x :- Nat,
            P :- (=> Nat Prop), tf :- (forall [k :- Nat] (P (subst (+ j k) v x)))]
          '(P (subst j v x)) '[(exact (tf 0))]))

(deftest rewrite-placeholders-and-explicit-proof
  ;; Lean Elab/Tactic/Rewrite.lean elabRewrite elaborates before matching.
  (proves 'rewrite_right_zero_hole '[n :- Nat] '(= (+ n 0) n) '[(rw [(Nat.add_zero _)])])
  (proves 'rewrite_comm_holes '[x :- Nat, y :- Nat] '(= (+ x y) (+ y x))
          '[(rw [(Nat.add_comm _ _)])])
  (a/theorem carry_holes [x :- Nat, y :- Nat, z :- Nat, h :- (= x y)]
             (= (+ x z) (+ y z)) (rw [h]))
  (proves 'rewrite_proof_holes '[x :- Nat, y :- Nat, z :- Nat, h :- (= x y)]
          '(= (+ x z) (+ y z)) '[(rw [(carry_holes _ _ _ h)])]))

(deftest have-infers-type-from-proof
  (proves 'inferred_have '[h :- True] 'True '[(have hh := h) (exact hh)]))
