;; Run full verification up to 221k with low fuel to find slow declarations
;; Uses 1M fuel limit — any declaration needing more than 1M reductions is suspicious

(ns cic.export.find-slow-full
  (:require [cic.export.storage :as storage]))

(defn -main [& _args]
  (let [store-path "/var/tmp/cic-lmdb-mathlib"
        branch "mathlib"
        low-fuel 1000000]  ;; 1M fuel
    (println "Opening LMDB store at" store-path)
    (let [store-map (storage/open-lmdb-store store-path)]
      (try
        (let [ctx (storage/prepare-verify store-map branch :log-file "/tmp/cic-find-slow-full.log")
              total (count (:decl-order ctx))
              end-idx (min 221000 total)]
          (println "Total:" total ". Verifying 0.." end-idx "with fuel=" low-fuel)
          ;; Verify in batch with stop-on-error=false to see all fuel-exceeded
          (let [result (storage/verify-batch! ctx end-idx
                         :verbose? true :fuel low-fuel :stop-on-error? false)]
            (println "\nDone:" (select-keys result [:ok :errors :idx]))
            (println "Error names:" @(:error-names ctx))
            (doseq [en @(:error-names ctx)]
              (println "  ERROR:" en))))
        (finally
          (storage/close-store store-map)
          (shutdown-agents))))))
