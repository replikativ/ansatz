(ns ansatz.datatype.cert
  "Certification runner for datatype derivations.

   This namespace remains outside the kernel. It turns an untrusted datatype
   derivation into a proof candidate, then asks the kernel-facing verifier to
   check that candidate."
  (:require [ansatz.datatype :as dt]
            [ansatz.kernel.env :as kenv]
            [ansatz.surface.elaborate :as elab]))

(defn certify
  "Search, reconstruct, elaborate, and strictly verify one datatype judgment.

   `certifier` is usually `(dt/certifier datatype template-spec)`.
   `goal-form` is `(fn [judgment proof-artifact] surface-goal-form)`.

   Returns the `kenv/verifies-report` map enriched with derivation context, or
   `{:ok? false :status :no-derivation}` when the relation has no solution."
  ([kernel-env datatype certifier goal-form judgment]
   (certify kernel-env datatype certifier goal-form judgment nil))
  ([kernel-env datatype certifier goal-form judgment opts]
   (let [answer (first (dt/solve datatype 1 [] judgment {:proof? true}))]
     (if-not answer
       {:ok? false
        :status :no-derivation
        :judgment judgment}
       (let [proof (:proof answer)
             proof-artifact (certifier proof)
             surface-goal (goal-form judgment proof-artifact)
             surface-proof (:term proof-artifact)
             goal-expr (elab/elaborate-check kernel-env surface-goal)
             proof-expr (elab/elaborate-check kernel-env surface-proof goal-expr)
             report (kenv/verifies-report kernel-env goal-expr proof-expr opts)]
         (assoc report
                :answer answer
                :derivation proof
                :proof-artifact proof-artifact
                :goal-form surface-goal
                :proof-form surface-proof
                :goal-expr goal-expr
                :proof-expr proof-expr))))))
