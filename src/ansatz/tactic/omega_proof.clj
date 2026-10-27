;; Compatibility facade for the single Frontend/Core decision procedure.
(ns ansatz.tactic.omega-proof
  (:require [ansatz.tactic.omega.frontend :as impl]))

(def omega impl/omega)
(def decides? impl/decides?)
(def reify-goal impl/reify-goal)
(def certify impl/certify)
(def show-problem impl/show-problem)

(defn solve-fm [reified]
  (when-let [result (impl/solve-fm reified)]
    (assoc result :num-vars (:numVars result) :proof-false (:proveFalse? result))))

;; Historical inspection hooks used by callers/tests. No alternate arithmetic.
(def omega-names @#'impl/omega-names)
(def reify-term @#'impl/reify-term)
(def mk-problem @#'impl/mk-problem)
(def mk-atom-table @#'impl/mk-atom-table)
(def add-inequality @#'impl/add-inequality)
(def add-equality @#'impl/add-equality)

(defn run-omega-solver [table problem]
  (let [[table result] (impl/run-omega-solver table problem)]
    [table (assoc result :num-vars (:numVars result) :proof-false (:proveFalse? result))]))

(def ^:dynamic *strict-div-bounds*
  "Deprecated compatibility binding: supported constructions always throw on faults."
  true)
