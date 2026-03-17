;; Trace slow declaration around 220k in mathlib verification
;; Run with: PATH=/usr/lib/jvm/java-25-openjdk-amd64/bin:$PATH clj -J--enable-native-access=ALL-UNNAMED -J-Xmx8g -J-Xss64m -M -i scripts/trace_slow_decl.clj -e '(ansatz.export.trace-slow/-main)'

(ns ansatz.export.trace-slow
  (:require [ansatz.export.storage :as storage]))

(defn -main [& _args]
  (let [store-path "/var/tmp/ansatz-lmdb-mathlib"
        branch "mathlib"]
    (println "Opening LMDB store at" store-path)
    (let [store-map (storage/open-lmdb-store store-path)]
      (try
        (println "Preparing verification context...")
        (let [ctx (storage/prepare-verify store-map branch :log-file "/tmp/ansatz-trace.log")
              total (count (:decl-order ctx))
              skip-to 219000]
          (println "Total declarations:" total)
          (println "Skipping to" skip-to "...")
          (storage/skip! ctx skip-to)
          (println "Skipped to" @(:idx ctx))
          ;; Now verify one-by-one with detailed timing
          (let [end-idx (min (+ skip-to 2000) total)]
            (loop []
              (when (< @(:idx ctx) end-idx)
                (let [i @(:idx ctx)
                      name-str (nth (:decl-order ctx) i)
                      t0 (System/nanoTime)
                      rt (Runtime/getRuntime)
                      mem-before (quot (- (.totalMemory rt) (.freeMemory rt)) 1048576)
                      result (storage/verify-one! ctx)
                      elapsed-ms (/ (- (System/nanoTime) t0) 1e6)
                      mem-after (quot (- (.totalMemory rt) (.freeMemory rt)) 1048576)]
                  (when (or (> elapsed-ms 1000)    ;; slow (>1s)
                            (> (- mem-after mem-before) 500)) ;; memory spike
                    (println (format "[%d] %s  %.1fms  mem=%dMB→%dMB (+%dMB)  status=%s  fuel=%s"
                                     i name-str elapsed-ms mem-before mem-after
                                     (- mem-after mem-before)
                                     (:status result)
                                     (or (:fuel-used result) "?"))))
                  (when (zero? (mod (inc i) 100))
                    (println (format "  ... %d ok=%d err=%d mem=%dMB"
                                     (inc i) @(:ok ctx) @(:errors ctx) mem-after)))
                  (recur))))))
        (finally
          (storage/close-store store-map)
          (shutdown-agents))))))
