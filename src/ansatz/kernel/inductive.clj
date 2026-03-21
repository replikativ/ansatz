;; Ansatz kernel for Clojure — Inductive type processing.

(ns ansatz.kernel.inductive
  "Processing of inductive type declarations."
  (:import [ansatz.kernel ConstantInfo]))

(defn check-inductive-import
  "Lightweight validation of an imported inductive declaration."
  [env ^ConstantInfo induct-ci ctor-cis rec-cis]
  (let [ind-name (.name induct-ci)]
    (doseq [^ConstantInfo ctor ctor-cis]
      (when (not= (.inductName ctor) ind-name)
        (throw (ex-info "Constructor references wrong inductive"
                        {:ctor (.name ctor) :expected ind-name :got (.inductName ctor)}))))
    (let [ctor-names (set (map #(.name ^ConstantInfo %) ctor-cis))]
      (doseq [^ConstantInfo rec rec-cis]
        (doseq [rule (.rules rec)]
          (when-not (ctor-names (.ctor ^ansatz.kernel.ConstantInfo$RecursorRule rule))
            (throw (ex-info "Recursor rule references unknown constructor"
                            {:recursor (.name rec) :ctor (.ctor ^ansatz.kernel.ConstantInfo$RecursorRule rule)
                             :known ctor-names}))))))
    (concat [induct-ci] ctor-cis rec-cis)))
