;; Copyright (c) 2026 Simmis GmbH. All rights reserved.
;; CIC kernel for Clojure — Inductive type processing.

(ns cic.kernel.inductive
  "Processing of inductive type declarations."
  (:require [cic.kernel.expr :as e]
            [cic.kernel.env :as env]
            [cic.kernel.level :as lvl]
            [cic.kernel.name :as name])
  (:import [cic.kernel ConstantInfo Name]))

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
          (when-not (ctor-names (.ctor ^cic.kernel.ConstantInfo$RecursorRule rule))
            (throw (ex-info "Recursor rule references unknown constructor"
                            {:recursor (.name rec) :ctor (.ctor ^cic.kernel.ConstantInfo$RecursorRule rule)
                             :known ctor-names}))))))
    (concat [induct-ci] ctor-cis rec-cis)))
