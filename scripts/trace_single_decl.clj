;; Trace a single declaration by index in the mathlib verification order
;; Run with: clj -J--enable-native-access=ALL-UNNAMED -J-Xmx8g -J-Xss64m -M -i scripts/trace_single_decl.clj -e '(cic.export.trace-single/-main "220201")'

(ns cic.export.trace-single
  (:require [cic.export.storage :as storage])
  (:import [cic.kernel TypeChecker Env ConstantInfo]))

(defn count-nodes [^cic.kernel.Expr e]
  "Count unique Expr objects (DAG nodes) in the expression."
  (let [visited (java.util.IdentityHashMap.)]
    (letfn [(go [^cic.kernel.Expr e]
              (when (and e (not (.containsKey visited e)))
                (.put visited e true)
                (case (.tag e)
                  (3) (do (go (.o0 e)) (go (.o1 e)))  ;; APP
                  (4 5) (do (go (.o1 e)) (go (.o2 e))) ;; LAM, FORALL
                  (6) (do (go (.o1 e)) (go (.o2 e)) (go (.o3 e))) ;; LET
                  (9) (go (.o1 e))  ;; MDATA
                  (10) (go (.o1 e)) ;; PROJ
                  nil)))]
      (go e)
      (.size visited))))

(defn -main [idx-str & _args]
  (let [target-idx (Long/parseLong idx-str)
        store-path "/var/tmp/cic-lmdb-mathlib"
        branch "mathlib"]
    (println "Opening LMDB store at" store-path)
    (let [store-map (storage/open-lmdb-store store-path)]
      (try
        (println "Preparing verification context...")
        (let [ctx (storage/prepare-verify store-map branch :log-file "/tmp/cic-trace-single.log")
              total (count (:decl-order ctx))
              decl-name (nth (:decl-order ctx) target-idx)]
          (println "Total declarations:" total)
          (println "Target:" target-idx decl-name)
          (println "Skipping to" target-idx "...")
          (storage/skip! ctx target-idx)
          (println "Skipped. Now resolving CI...")
          (let [^ConstantInfo ci ((:resolve-fn ctx) decl-name)
                tag (.tag ci)]
            (println "CI tag:" tag "name:" (.toString (.name ci)))
            (println "Type node count:" (count-nodes (.type ci)))
            (when (.value ci)
              (println "Value node count:" (count-nodes (.value ci))))
            (println "Starting type check with fuel 200M, timeout 120s...")
            (let [t0 (System/nanoTime)
                  f (future
                      (try
                        (let [^objects result-arr (TypeChecker/checkConstantFuelStats
                                                   (:env ctx) ci 200000000)]
                          {:result result-arr})
                        (catch Exception e
                          {:error (.getMessage e)})))
                  result (deref f 120000 :timeout)
                  elapsed-ms (/ (- (System/nanoTime) t0) 1e6)]
              (println (format "Elapsed: %.1fms" elapsed-ms))
              (if (= result :timeout)
                (do
                  (println "TIMEOUT after 120s!")
                  (future-cancel f))
                (do
                  (println "Result:" result)
                  (when-let [arr (:result result)]
                    (println "Fuel used:" (aget ^objects arr 0))
                    (println "Stats:" (into {} (aget ^objects arr 1)))
                    (let [trace (vec (aget ^objects arr 2))]
                      (println "Trace entries:" (count trace))
                      (doseq [t (take 50 trace)]
                        (println "  " t)))
                    (when (aget ^objects arr 3)
                      (println "Error:" (aget ^objects arr 3)))))))))
        (finally
          (storage/close-store store-map)
          (shutdown-agents))))))
