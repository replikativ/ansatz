;; Import full mathlib NDJSON into LMDB store at /var/tmp/cic-lmdb-mathlib
;; Run with: clj -X:import-mathlib
;; Or:       clj --enable-native-access=ALL-UNNAMED -Xmx16g -M -m cic.export.import-mathlib

(ns cic.export.import-mathlib
  (:require [cic.export.storage :as storage]))

(defn -main [& _args]
  (let [store-path "/var/tmp/cic-lmdb-mathlib"
        ndjson-path "/home/christian-weilbach/Development/cic-clj/test-data/mathlib.ndjson"
        log-file "/tmp/cic-import.log"]
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
