;; Internal second phase of generate-bundle.py. Never promotes a candidate.
(require '[ansatz.bundle-validation :as validation])

(try
  (when-not (= 1 (count *command-line-args*))
    (throw (ex-info "Expected one staging directory" {})))
  (let [report (validation/validate-candidate! (first *command-line-args*))]
    (println (select-keys report [:kernel :overlap-count :consumer :artifact/cohort :publication])))
  (shutdown-agents)
  (catch Throwable error
    ;; Print selected gate context, not an entire replay Env or parser store.
    ;; Message/root text are not a general output budget; the new role samples are capped.
    (binding [*out* *err*]
      (println {:bundle-generation-error (.getMessage error)
                :details (select-keys (ex-data error)
                                     [:stage :role :root :name :left :right :missing :kernel-role
                                      :metadata-profile :missing-edge-count :missing-root-count
                                      :missing-edge-sample :missing-root-sample :samples-truncated? :sample-text-truncated?])}))
    (System/exit 1)))
