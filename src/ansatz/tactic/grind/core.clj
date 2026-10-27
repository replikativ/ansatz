(ns ansatz.tactic.grind.core
  "Lean/Meta/Tactic/Grind/Core.lean closeGoalWithValuesEq, checkout v4.33.1."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.instance :as instance]
            [ansatz.tactic.grind.action :as action]
            [ansatz.tactic.grind.proof :as proof]))

(defn- c [n] (e/const' (name/from-string n) []))

(defn close-goal-with-values-eq [gs st lhs rhs]
  (let [type (tc/infer-type st lhs)
        p (e/app* (e/const' (name/from-string "Eq") [(lvl/succ lvl/zero)]) type lhs rhs)
        inst (instance/synthesize* st (:env st) (instance/index-for (:env st))
                                   (e/app (c "Decidable") p) 0)
        _ (when-not inst (action/fail! "literal equality decision unavailable" {:lhs lhs :rhs rhs}))
        value (#'tc/cached-whnf st (e/app* (c "Decidable.decide") p inst))
        _ (when-not (= value (c "Bool.false"))
            (action/fail! "literal equality decision did not reduce to false" {:lhs lhs :rhs rhs}))
        ;; The bundled Init exports of_decide_eq_false, but not the convenience
        ;; eq_false_of_decide used by Lean Core. Its Not proof closes identically.
        hnp (e/app* (c "of_decide_eq_false") p inst
                    (proof/mk-eq-refl st (c "Bool.false")))
        hp (proof/mk-eq-proof gs st lhs rhs)]
    (e/app hnp hp)))
