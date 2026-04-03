;; Tactic layer — decide tactic.

(ns ansatz.tactic.decide
  "The `decide` tactic closes goals of decidable propositions by:
   1. Resolving a Decidable instance for the goal type
   2. Constructing `@of_decide_eq_true P inst (Eq.refl Bool.true)`
   3. The kernel verifies this by evaluating `decide P inst` to `true`"
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.proof :as proof]
            [ansatz.tactic.instance :as instance])
  (:import [ansatz.kernel TypeChecker]))

;; ============================================================
;; Well-known names
;; ============================================================

(def ^:private of-decide-eq-true-name (name/from-string "of_decide_eq_true"))
(def ^:private eq-refl-name (name/from-string "Eq.refl"))
(def ^:private bool-name (name/from-string "Bool"))
(def ^:private bool-true-name (name/from-string "Bool.true"))
(def ^:private decidable-decide-name (name/from-string "Decidable.decide"))
(def ^:private decidable-name (name/from-string "Decidable"))

;; ============================================================
;; decide tactic
;; ============================================================

(defn- build-decide-proof
  "Build the proof term `@of_decide_eq_true P inst (Eq.refl Bool.true)`.
   Returns the Ansatz expression."
  [_env prop inst]
  (let [u1 (lvl/succ lvl/zero)
        bool-type (e/const' bool-name [])
        bool-true (e/const' bool-true-name [])
        eq-refl-proof (e/app* (e/const' eq-refl-name [u1]) bool-type bool-true)]
    (e/app* (e/const' of-decide-eq-true-name []) prop inst eq-refl-proof)))

(defn- verify-decide
  "Verify that decide P inst reduces to Bool.true.
   Returns true if it does, false otherwise."
  [env prop inst]
  (let [st (tc/mk-tc-state env)
        decide-term (e/app* (e/const' decidable-decide-name []) prop inst)
        result (#'tc/cached-whnf st decide-term)
        bool-true (e/const' bool-true-name [])]
    (= result bool-true)))

(defn- get-instance-index
  "Get or build the instance index, caching it in the proof state."
  [ps]
  (if-let [idx (:instance-index ps)]
    [ps idx]
    (let [idx (instance/build-instance-index (:env ps))]
      [(assoc ps :instance-index idx) idx])))

(defn decide
  "Close the current goal by constructing a decision proof.

   1. Resolve a Decidable instance for the goal type
   2. Verify that `decide P inst` evaluates to `true`
   3. Assign the goal with the proof term

   Returns updated proof state."
  [ps]
  (let [goal (proof/current-goal ps)
        _ (when-not goal
            (throw (ex-info "Tactic error: No goals" {:kind :tactic-error})))
        [ps idx] (get-instance-index ps)
        env (:env ps)
        prop (:type goal)
        decidable-goal (e/app (e/const' decidable-name []) prop)
        inst (instance/synthesize env idx decidable-goal)]
    ;; Verify the decision evaluates to true
    (when-not (verify-decide env prop inst)
      (throw (ex-info "Tactic error: decide failed — proposition is false or undecidable at this point"
                      {:kind :tactic-error :prop prop})))
    (let [proof-term (build-decide-proof env prop inst)]
      ;; Double-check: type-check the proof
      (let [tc (TypeChecker. env)
            inferred (.inferType tc proof-term)]
        (when-not (.isDefEq tc inferred prop)
          (throw (ex-info "Tactic error: decide proof does not type-check"
                          {:kind :tactic-error :expected prop :inferred inferred}))))
      (-> (proof/assign-mvar ps (:id goal) {:kind :exact :term proof-term})
          (proof/record-tactic :decide [] (:id goal))))))
