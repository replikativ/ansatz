(ns ansatz.meta.match.case-values
  "Lean/Meta/Match/CaseValues.lean, caseValue/caseValues (55f80e10a3)."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.meta.constructions.util :as u]
            [ansatz.meta.tactic.cases :as c]
            [ansatz.tactic.instance :as inst]))

(defn get-nat-value?
  "Lean/Meta/LitValues.lean getNatValue?: raw Nat or Nat's OfNat encoding."
  [ctx expr]
  (let [expr (loop [x expr] (if (e/mdata? x) (recur (e/mdata-expr x)) x))]
    (if (e/lit-nat? expr) (e/lit-nat-val expr)
        (let [[f args] (e/get-app-fn-args expr)]
          (when (and (e/const? f) (= "OfNat.ofNat" (str (e/const-name f)))
                     (= 3 (count args)) (e/lit-nat? (nth args 1)))
            (let [type (u/whnf ctx (first args))]
              (when (and (e/const? type) (= "Nat" (str (e/const-name type))))
                (e/lit-nat-val (nth args 1)))))))))

(defn case-value [ctx id fvar-id value]
  (c/with-goal! ctx id)
  (let [target (c/goal-type ctx id) x (e/fvar fvar-id)
        value (if-let [n (get-nat-value? ctx value)] (e/lit-nat n) value)
        eq (u/mk-eq ctx x value)
        neq (u/app (u/const' "Not" []) [eq])
        then-id (c/fresh-mvar! ctx (e/forall' "h" eq (e/lift target 1 0) :default))
        else-id (c/fresh-mvar! ctx (e/forall' "h" neq (e/lift target 1 0) :default))
        dec-goal (u/app (u/const' "Decidable" []) [eq])
        dec (inst/synthesize* @ctx (:env @ctx) (inst/index-for (:env @ctx)) dec-goal 0)]
    (when-not dec (c/tactic-error! "caseValue: no decidable equality instance" {:type eq}))
    (c/assign! ctx id (u/app (u/const' "dite" [(u/get-level ctx target)])
                             [target eq dec (e/mvar then-id) (e/mvar else-id)]))
    [then-id else-id]))

(defn case-values [ctx id fvar-id values need-hyps]
  (when (empty? values) (c/tactic-error! "caseValues: list of values must not be empty" {}))
  (loop [id id values (seq values) hs [] subgoals []]
    (let [[then-id else-id] (case-value ctx id fvar-id (first values))
          then-id (reduce (fn [id h] (c/clear! ctx id h)) then-id hs)
          [h then-id] (c/intro1 ctx then-id)
          [s then-id] (c/subst-core ctx then-id (e/fvar-id h) false {})
          subgoals (conj subgoals {:mvar-id then-id :new-hs [] :subst s})
          [h else-id] (c/intro1 ctx else-id)
          else-id (if need-hyps else-id (c/clear! ctx else-id (e/fvar-id h)))
          hs (if need-hyps (conj hs (e/fvar-id h)) hs)]
      (if (next values)
        (recur else-id (next values) hs subgoals)
        (conj subgoals {:mvar-id else-id :new-hs hs :subst {}})))))
