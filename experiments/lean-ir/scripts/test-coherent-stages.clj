;; Bounded definitions/model gate. Run from experiments/lean-ir with src, test,
;; main-library sources, coherent Java classes and dependencies on the classpath.
(require '[clojure.test :as t] '[clojure.java.io :as io])
(def observed (atom #{}))
(defmethod t/report :begin-test-var [event] (swap! observed conj (:var event)))
(defmethod t/report :fail [event]
  (t/inc-report-counter :fail)
  (println "ASSERTION_FAILURE" (:file event) (:line event)))
(defmethod t/report :error [event]
  (t/inc-report-counter :error)
  (println "TEST_ERROR" (:file event) (:line event))
  (loop [cause (:actual event) remaining 8]
    (when (and cause (pos? remaining))
      (println (.getName (class cause)))
      (doseq [frame (take 5 (.getStackTrace ^Throwable cause))] (println (str frame)))
      (recur (.getCause ^Throwable cause) (dec remaining)))))
(try
  ;; Loading definitions must never call construct!, run!, restore or a guest.
  (doseq [n '[prototype.coherent-source-preparation prototype.coherent-helper-value
              prototype.coherent-typed-eio prototype.coherent-execution
              prototype.coherent-stage-guards prototype.coherent-campaign
              prototype.coherent-stage-guards-test prototype.coherent-owner-ledger-test]]
    (require n))
  (assert (nil? ((ns-resolve 'prototype.coherent-campaign 'checkpoint))))
  (let [vars (set (filter #(-> % meta :test) (mapcat #(vals (ns-publics %)) '[prototype.coherent-stage-guards-test prototype.coherent-owner-ledger-test])))
        _ (assert (= 20 (count vars)))
        counters (binding [t/*report-counters* (ref t/*initial-report-counters*)]
                   (t/test-vars (sort-by #(str (:name (meta %))) vars))
                   @t/*report-counters*)]
    (assert (= vars @observed))
    (assert (zero? (+ (:fail counters) (:error counters))))
    (assert (= 20 (:test counters)))
    (assert (nil? ((ns-resolve 'prototype.coherent-campaign 'checkpoint))))
    (println (assoc counters :scope "definitions-and-twenty-protocol-models-only"))
    (println "COHERENT_STAGE_MODELS_PASS")
    (shutdown-agents)
    (System/exit 0))
  (catch Throwable failure
    (println "COHERENT_STAGE_MODELS_FAILURE" (.getName (class failure)))
    (loop [cause failure remaining 8]
      (when (and cause (pos? remaining))
        (println (.getName (class cause)))
        (doseq [frame (take 5 (.getStackTrace ^Throwable cause))] (println (str frame)))
        (recur (.getCause ^Throwable cause) (dec remaining))))
    (shutdown-agents)
    (System/exit 2)))
