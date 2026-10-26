;; Small native-CI fixtures and modeled controller owners; no Init/Source restore.
(require '[clojure.test :as t]
         'prototype.compact-import-check-test 'prototype.coherent-campaign-phase-test)
(def seen (atom #{}))
(defmethod t/report :begin-test-var [event] (swap! seen conj (:var event)))
(defmethod t/report :fail [event]
  (t/inc-report-counter :fail)
  (println "BOUNDED_ASSERTION_FAILURE" (:file event) (:line event)))
(defmethod t/report :error [event]
  (t/inc-report-counter :error)
  (println "BOUNDED_TEST_ERROR" (.getName (class (:actual event)))))
(let [nss ['prototype.compact-import-check-test 'prototype.coherent-campaign-phase-test]
      expected (set (for [n nss [_ v] (ns-publics n) :when (:test (meta v))] v))
      result (apply t/run-tests nss)]
  (shutdown-agents)
  (System/exit (if (and (= 13 (count expected) (:test result)) (= expected @seen)
                       (zero? (+ (:fail result) (:error result)))) 0 1)))
