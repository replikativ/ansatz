(ns native-project-service-models-v1
  "Preflight rejection models only; these launch no compiler or JVM engine."
  (:require [clojure.test :refer [deftest is run-tests]]
            [native-project-service-v1 :as service])
  (:import [java.nio.file Path]))
(deftest unconfigured-loaders-cannot-open-build-or-runtime
  (doseq [value [nil {} {:ready true} (service/->Loader)]]
    (is (thrown? Exception (service/load-project! value "unused-project")))))
(deftest configuration-rejects-missing-cache-or-files-before-effects
  (is (thrown? Exception (service/configure! {} {})))
  (is (thrown? Exception (service/configure! {} {:cache "unused-cache" :native-reference? nil}))))
(deftest malformed-code-pins-reject-before-reading-helper-bytes
  (let [absent (Path/of "absent-model-helper.py" (make-array String 0))]
    (doseq [pin [nil "" "not-a-sha" (apply str (repeat 64 "g"))]]
      (is (thrown? Exception (#'service/file-pin! absent pin))))))
(deftest exceptional-build-stops-owned-process-and-preserves-handle-and-interruption
  (let [stops (atom 0) process (proxy [java.lang.Process] [] (isAlive [] true))
        slot (object-array [process]) journal {:process-slot slot} prior (Thread/interrupted)]
    (try
      (with-redefs-fn {#'service/stop-process! (fn [actual] (is (identical? process actual)) (swap! stops inc))}
        #(let [failure (#'service/abort-build! journal (InterruptedException. "modeled cancellation"))
                interrupted (.isInterrupted (Thread/currentThread))]
           ;; Capture before clojure.test reporting/locking can consume it; clear
           ;; before reporting so the test transport itself stays healthy.
           (Thread/interrupted)
           (is (= 1 @stops))
           (is (identical? slot (:process-slot (ex-data failure))))
           (is interrupted)))
      (finally (Thread/interrupted) (when prior (.interrupt (Thread/currentThread)))))))
(defn check! [] (run-tests 'native-project-service-models-v1))
