(ns ansatz.eqns
  "Equation inventory following Lean/Meta/Eqns.lean (registerEqnThms/getEqnsFor?)
   and Lean/Elab/PreDefinition/Eqns.lean, checkout v4.33.1.
   The eager surface elaborator records admitted equations; direct inventories keep
   auxiliary ownership separate."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

(defn- decl-name [n]
  (if (instance? ansatz.kernel.Name n) n (name/from-string (str n))))

(defn eqns-for
  "Ordered admitted equations owned by this declaration (not its auxiliary matchers).
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

(defn get-unfold-eqn-for?
  "Lean 4.33.1 Meta/Eqns.lean getUnfoldEqnFor?: existing theorem lookup.
   Generation of missing unfold equations (mkUnfoldEq) is not yet supported."
  [environment n]
  ;; eq_unfold is the local well-founded compiler's existing equation spelling.
  (some (fn [suffix]
          (let [eqn (name/from-string (str (name/->string (decl-name n)) suffix))]
            (when (env/lookup environment eqn) eqn)))
        [".eq_def" ".eq_unfold"]))

(defn already-generated?
  "Lean Meta/Eqns.lean alreadyGenerated?: imported sequential eq_1, eq_2, ….
   Never includes auxiliary matcher equations or guesses conditional variants."
  [environment n]
  (let [n (decl-name n)]
    (loop [i 1 equations []]
      (let [equation (name/mk-str n (str "eq_" i))
            ci (env/lookup environment equation)]
        (if (and ci (= :thm (env/ci-tag ci)))
          (recur (inc i) (conj equations equation))
          (when (seq equations) equations))))))

(defn get-eqns-for?
  "Lean getEqnsFor?Core: prefer the eager local inventory; recognize imported equations."
  [environment n]
  (let [equations (eqns-for environment n)]
    (if (some? equations) equations (already-generated? environment n))))
