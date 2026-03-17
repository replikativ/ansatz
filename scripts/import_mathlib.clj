;; Import full mathlib NDJSON into LMDB store at /var/tmp/ansatz-lmdb-mathlib
;; Run with: clj -X:import-mathlib
;; Or:       clj --enable-native-access=ALL-UNNAMED -Xmx16g -M -m ansatz.export.import-mathlib

(ns ansatz.export.import-mathlib
  (:require [ansatz.export.storage :as storage]))

(defn -main [& _args]
  (let [store-path "/var/tmp/ansatz-lmdb-mathlib"
        ndjson-path "/home/christian-weilbach/Development/ansatz/test-data/mathlib.ndjson"
        log-file "/tmp/ansatz-import.log"]
    (println "Opening LMDB store at" store-path)
    (let [store-map (storage/open-lmdb-store store-path)]
      (try
        (println "Starting import, log:" log-file)
        (println "Monitor with: tail -f" log-file)
        (let [result (storage/import-ndjson-streaming!
                      store-map ndjson-path "mathlib"
                      :verbose? true
                      :log-file log-file)]
          (println "Import complete!")
          (println "Result:" (pr-str result)))
        (finally
          (storage/close-store store-map)
          (shutdown-agents))))))
