(ns ansatz.eqns
  "Equation inventory following Lean/Meta/Eqns.lean (registerEqnThms/getEqnsFor?)
   and Lean/Elab/PreDefinition/Eqns.lean, checkout v4.33.1.
   The eager surface elaborator records admitted equations; lookup never scans names."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

(defn- decl-name [n]
  (if (instance? ansatz.kernel.Name n) n (name/from-string (str n))))

(defn eqns-for
  "Ordered admitted equation names, including the definition's matcher equations.
   nil means no inventory; [] is a recorded empty inventory. Inspect errors-for too."
  [env n]
  (get (env/get-extension env :eqns {}) (decl-name n)))

(defn errors-for [env n]
  (get (env/get-extension env :eqns-errors {}) (decl-name n) []))

(defn register-eqn-thms
  "Record only installed theorems. Errors are data so the extension can be persisted.
   Like Lean registerEqnThms, this records provenance rather than admitting declarations."
  [env n equations errors]
  (let [n (decl-name n) equations (vec (distinct (map decl-name equations)))
        errors (mapv #(assoc (ex-data %) :message (.getMessage ^Throwable %)) errors)]
    (doseq [eqn equations]
      (let [ci (env/lookup env eqn)]
        (when-not (and ci (= :thm (env/ci-tag ci)))
          (throw (ex-info "Equation inventory refers to an uninstalled theorem"
                          {:kind :eqns-metadata-error :definition n :equation eqn})))))
    (-> env
        (env/update-extension :eqns {} assoc n equations)
        (env/update-extension :eqns-errors {} assoc n errors))))
