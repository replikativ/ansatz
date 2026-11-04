(ns ansatz.tactic.simp-location-test
  "Lean pairs: test/lean/simp_location.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.surface.elaborate :as elab]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.extract :as extract]
            [ansatz.tactic.simp :as simp]))

(use-fixtures :once
  (fn [t]
    (a/load-init!)
    (binding [a/*verbose* false *ns* (the-ns 'ansatz.tactic.simp-location-test)]
      (t))))

(defn- proves? [form]
  (let [before (a/env)]
    (try (eval form) true
         (finally (reset! a/ansatz-env before)))))

(deftest contradictory-location-closes-before-remaining-locations
  (doseq [tactic ['(simp at h1 h2) '(simp at h1 ⊢) '(simp at *)
                  '(simp only [Bool.false_eq_true] at h1 h2)
                  '(simp_all)]]
    (is (proves? `(a/theorem ~'bool-contradictory-locations [~'b :- ~'Bool, ~'c :- ~'Bool]
                             (~'=> (~'= false true) (~'= ~'c true) (~'= ~'b true))
                             (~'intro ~'h1 ~'h2) ~tactic)))))

(deftest mixed-locations-check-progress-once
  (doseq [locs ['(h1 h2) '(h2 h1) '(h1 h2 ⊢) '(*)]]
    (is (proves? (list 'a/theorem 'mixed-simp-locations
                       '[P :- Prop, Q :- Prop, h1 :- P, h2 :- (And Q True)]
                       'Q (cons 'simp (cons 'at locs)) '(exact h2)))))
  (is (proves? '(a/theorem target-only-progress
                           [P :- Prop, h :- P] (And P True)
                           (simp at h ⊢) (exact h)))))

(deftest unchanged-locations-fail
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"made no progress"
                        (eval '(a/theorem unchanged-simp-locations
                                          [P :- Prop, Q :- Prop, h1 :- P, h2 :- Q]
                                          P (simp at h1 h2) (exact h1))))))

(deftest all-location-names-are-resolved-before-simplification
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"no hypothesis named missing"
                        (eval '(a/theorem missing-simp-location
                                          [h :- (= false true)] False
                                          (simp at h missing))))))

(deftest dsimp-locations-share-progress-and-closure
  (is (proves? '(a/theorem contradictory-dsimp-only-locations
                           [P :- Prop, h1 :- False, h2 :- P] P (dsimp only at h1 h2))))
  (is (proves? '(a/theorem contradictory-dsimp-locations
                           [P :- Prop, h1 :- False, h2 :- P] P (dsimp at h1 h2))))
  (is (proves? '(a/theorem contradictory-dsimp-target
                           [P :- Prop, h :- False] P (dsimp at h ⊢))))
  (is (proves? '(a/theorem contradictory-dsimp-wildcard
                           [P :- Prop, h :- False] P (dsimp at *))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"made no progress"
                        (eval '(a/theorem unchanged-dsimp-locations
                                          [P :- Prop, h :- P] P (dsimp at h) (exact h))))))

(deftest dsimp-matcher-location-closure-only
  ;; Acceptance/closure coverage only: exact accepts definitionally equal types.
  ;; The structural reducer can leave Bool.casesOn here, unlike Lean's guard_hyp.
  (is (proves? '(a/theorem dsimp-matcher-location-closure
                           [P :- Prop, Q :- Prop, h1 :- P,
                            h2 :- (match true [true Q] [false True])]
                           Q (dsimp at h1 h2) (exact h2)))))

(deftest closing-a-location-preserves-sibling-goals
  (is (proves? '(a/theorem simp-location-siblings
                           [P :- Prop, h :- (= false true), hp :- P]
                           (And P P) (constructor) (simp at h hp) (exact hp)))))

(deftest replacements-remain-available-after-target-simplification
  (is (proves? '(a/theorem multiple-simp-replacements
                           [P :- Prop, Q :- Prop, h1 :- (And P True), h2 :- (And Q True)]
                           (And P Q) (simp at h2 h1 ⊢)
                           (constructor) (exact h1) (exact h2))))
  (is (proves? '(a/theorem simp-target-closes-with-pending-replacements
                           [P :- Prop, h :- (And P True)] (And True True)
                           (simp at h ⊢)))))

(deftest dsimp-replaces-the-local-type-without-renaming-the-local
  (let [type (elab/elaborate (a/env)
                             '(forall [P :- Prop, Q :- Prop, h1 :- P,
                                       h2 :- (let [R Q] R)] Q))
        [ps _] (proof/start-proof (a/env) type)
        ps (a/run-tactic ps '(intro P Q h1 h2))
        before (:lctx (proof/current-goal ps))
        id-of (fn [lctx n] (first (for [[id d] lctx :when (= n (:name d))] id)))
        h2 (id-of before "h2")
        q (id-of before "Q")
        ps (a/run-tactic ps '(dsimp at h1 h2))
        after (:lctx (proof/current-goal ps))]
    (is (= h2 (id-of after "h2")))
    (is (not= (get-in before [h2 :type]) (get-in after [h2 :type])))
    (is (= (e/fvar q) (get-in after [h2 :type])))))

(deftest wildcard-ignores-implementation-detail-dependencies
  (let [type (elab/elaborate (a/env)
                             '(forall [P :- Prop, h :- False, k :- (= False h h)] P))
        [ps _] (proof/start-proof (a/env) type)
        ps (a/run-tactic ps '(intro P h k))
        g (proof/current-goal ps)
        id-of (fn [n] (first (for [[id d] (:lctx g) :when (= n (:name d))] id)))
        h (id-of "h")
        k (id-of "k")]
    (is (= [k] (simp/get-nondep-prop-hyps ps)))
    (let [ps (assoc-in ps [:meta-mctx :decls (:id g) :lctx k :implementation-detail] true)]
      (is (= [h] (simp/get-nondep-prop-hyps ps)))
      (doseq [tactic ['(simp at *) '(dsimp at *)]]
        (let [closed (a/run-tactic ps tactic)]
          (is (empty? (:goals closed)))
          (is (some? (extract/verify closed))))))))
