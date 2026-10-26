;; Explicit optional compiler lane. Missing Pattern is a failure, never a skip.
(require '[clojure.test :as t] 'prototype.typed-tail-test)
(def seen (atom #{}))
(defmethod t/report :begin-test-var [event] (swap! seen conj (:var event)))
(defmethod t/report :fail [event]
  (t/inc-report-counter :fail)
  (println "TYPED_TAIL_ASSERTION_FAILURE" (:file event) (:line event)))
(defmethod t/report :error [event]
  (t/inc-report-counter :error)
  (println "TYPED_TAIL_TEST_ERROR" (.getName (class (:actual event)))))
(let [n 'prototype.typed-tail-test
      expected (set (for [[_ v] (ns-publics n) :when (:test (meta v))] v))
      result (t/run-tests n)]
  (shutdown-agents)
  (System/exit (if (and (= 8 (count expected) (:test result)))
                (if (and (= expected @seen) (zero? (+ (:fail result) (:error result)))) 0 1)
                1)))
