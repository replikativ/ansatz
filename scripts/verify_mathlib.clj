;; Verify mathlib from LMDB store at /var/tmp/ansatz-lmdb-mathlib
;; Saves progress to /tmp/ansatz-verify-checkpoint.edn so verification can be resumed.
;; Run with: clj -J--enable-native-access=ALL-UNNAMED -J-Xmx16g -J-Xss64m -M -i scripts/verify_mathlib.clj -e '(ansatz.export.verify-mathlib/-main)'

(ns ansatz.export.verify-mathlib
  (:require [ansatz.export.storage :as storage]))

(defn -main [& _args]
  (let [store-path "/var/tmp/ansatz-lmdb-mathlib"
        branch "mathlib"
        log-file "/tmp/ansatz-verify.log"
        checkpoint-file "/tmp/ansatz-verify-checkpoint.edn"]
    (println "Opening LMDB store at" store-path)
    (let [store-map (storage/open-lmdb-store store-path)]
      (try
        (println "Preparing verification context...")
        (let [ctx (storage/prepare-verify store-map branch :log-file log-file)
              total (count (:decl-order ctx))
              batch-size 50000]
          (println "Total declarations:" total)
          (println "Log:" log-file)
          (println "Monitor: tail -f" log-file)
          (println "Starting verification in batches of" batch-size "...")
          (loop []
            (let [idx @(:idx ctx)]
              (when (< idx total)
                (let [n (min batch-size (- total idx))
                      result (storage/verify-batch! ctx n :verbose? true)]
                  (spit checkpoint-file (pr-str result))
                  (println "Checkpoint saved:" checkpoint-file)
                  (recur)))))
          (let [final {:ok @(:ok ctx) :errors @(:errors ctx)
                       :total total :done? true
                       :error-names @(:error-names ctx)}]
            (println "Verification complete:" final)
            (spit checkpoint-file (pr-str final))
            (spit "/tmp/ansatz-verify-errors.edn"
                  (pr-str @(:error-names ctx)))))
        (finally
          (storage/close-store store-map)
          (shutdown-agents))))))
