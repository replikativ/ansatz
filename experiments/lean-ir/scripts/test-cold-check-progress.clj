;; Small native-CI fixtures and modeled controller owners; no Init/Source restore.
(require '[clojure.test :as t]
         'prototype.compact-import-check-test 'prototype.coherent-campaign-phase-test
         'prototype.module-store-test 'prototype.module-data-test 'prototype.typed-ir-test)
(def seen (atom #{}))
(defmethod t/report :begin-test-var [event] (swap! seen conj (:var event)))
(defmethod t/report :fail [event]
  (t/inc-report-counter :fail)
  (println "BOUNDED_ASSERTION_FAILURE" (:file event) (:line event)))
(defmethod t/report :error [event]
  (t/inc-report-counter :error)
  (println "BOUNDED_TEST_ERROR" (.getName (class (:actual event)))))
(let [nss ['prototype.compact-import-check-test 'prototype.coherent-campaign-phase-test
           'prototype.module-store-test 'prototype.typed-ir-test]
      targeted [#'prototype.module-data-test/hexadecimal-decoding-preserves-values-carriers-and-errors]
      expected (into (set (for [n nss [_ v] (ns-publics n) :when (:test (meta v))] v)) targeted)
      result (apply t/run-tests nss)
      targeted-result (binding [t/*report-counters* (ref t/*initial-report-counters*)]
                        (t/test-vars targeted)
                        (t/do-report (assoc @t/*report-counters* :type :summary))
                        @t/*report-counters*)]
  (shutdown-agents)
  (System/exit (if (and (= 34 (count expected) (+ (:test result) (:test targeted-result))) (= expected @seen)
                       (zero? (+ (:fail result) (:error result) (:fail targeted-result) (:error targeted-result)))) 0 1)))
