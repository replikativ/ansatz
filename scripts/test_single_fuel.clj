;; Test a single declaration with specific fuel level
(ns ansatz.export.test-single-fuel
  (:require [ansatz.export.storage :as storage])
  (:import [ansatz.kernel TypeChecker Env ConstantInfo]))

(defn -main [idx-str fuel-str & _args]
  (let [target-idx (Long/parseLong idx-str)
        fuel (Long/parseLong fuel-str)
        store-path "/var/tmp/ansatz-lmdb-mathlib"]
    (println "Opening LMDB store...")
    (let [store-map (storage/open-lmdb-store store-path)]
      (try
        (let [ctx (storage/prepare-verify store-map "mathlib" :log-file "/tmp/ansatz-test-fuel.log")
              decl-name (nth (:decl-order ctx) target-idx)]
          (println "Target:" target-idx decl-name "fuel:" fuel)
          (storage/skip! ctx target-idx)
          (let [t0 (System/nanoTime)
                result (storage/verify-one! ctx :fuel fuel)
                elapsed-ms (/ (- (System/nanoTime) t0) 1e6)]
            (println (format "Elapsed: %.1fms" elapsed-ms))
            (println "Status:" (:status result))
            (println "Fuel used:" (:fuel-used result))
            (when (:error result)
              (println "Error:" (:error result)))
            (when-let [stats (:stats result)]
              (println "Stats:" stats))
            (when-let [trace (:trace result)]
              (println "Trace entries:" (count trace))
              (println "Last 10 trace entries:")
              (doseq [t (take-last 10 trace)]
                (println "  " t)))))
        (finally
          (storage/close-store store-map)
          (shutdown-agents))))))
