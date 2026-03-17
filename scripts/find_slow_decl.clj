;; Find slow declarations by skipping to near the problem area
;; and verifying one at a time with a timeout

(ns ansatz.export.find-slow
  (:require [ansatz.export.storage :as storage])
  (:import [ansatz.kernel TypeChecker Env ConstantInfo]))

(defn -main [& _args]
  (let [store-path "/var/tmp/ansatz-lmdb-mathlib"
        branch "mathlib"
        skip-to 220200]
    (println "Opening LMDB store at" store-path)
    (let [store-map (storage/open-lmdb-store store-path)]
      (try
        (let [ctx (storage/prepare-verify store-map branch :log-file "/tmp/ansatz-find-slow.log")
              total (count (:decl-order ctx))]
          (println "Total:" total ". Skipping to" skip-to "...")
          (storage/skip! ctx skip-to)
          (println "Skipped. Starting verification...")
          (flush)
          (let [end-idx (min (+ skip-to 200) total)]
            (loop []
              (when (< @(:idx ctx) end-idx)
                (let [i @(:idx ctx)
                      name-str (nth (:decl-order ctx) i)
                      _ (println (format "Checking [%d] %s ..." i name-str))
                      _ (flush)
                      t0 (System/nanoTime)
                      result (storage/verify-one! ctx :fuel 200000000)
                      elapsed-ms (/ (- (System/nanoTime) t0) 1e6)
                      rt (Runtime/getRuntime)
                      mem (quot (- (.totalMemory rt) (.freeMemory rt)) 1048576)]
                  (println (format "  -> %.1fms  status=%s  fuel=%s  mem=%dMB"
                                   elapsed-ms (:status result)
                                   (or (:fuel-used result) "?") mem))
                  (when-let [trace (:trace result)]
                    (when (> (count trace) 10)
                      (println (format "  trace (%d entries): %s ... %s"
                                       (count trace)
                                       (str (take 5 trace))
                                       (str (take-last 5 trace))))))
                  (flush)
                  (recur))))))
        (finally
          (storage/close-store store-map)
          (shutdown-agents))))))
