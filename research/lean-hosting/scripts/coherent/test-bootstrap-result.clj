;; Small data/model test; run in an existing REPL, no project restore or launch.
(ns coherent-bootstrap-result-test
  (:require [clojure.java.io :as io] [clojure.test :as t]))

(let [source (io/file (.getParentFile (io/file *file*)) "bootstrap.clj")
      forms (with-open [reader (java.io.PushbackReader. (io/reader source))]
              (loop [out []]
                (let [form (read {:eof ::eof} reader)]
                  (if (= ::eof form) out (recur (conj out form))))))]
  ;; Authenticate shape before evaluating definitions: NEVER evaluate the launch
  ;; form. The scratch namespace prevents altering an existing bootstrap cohort.
  (assert (= 'ns (ffirst forms)))
  (assert (= 'let (first (last forms))))
  (binding [*ns* *ns*]
    (eval (cons 'ns (cons 'coherent-bootstrap-result-model (nnext (first forms)))))
    (doseq [form (butlast (rest forms))] (eval form))))

(def verify-result (ns-resolve 'coherent-bootstrap-result-model 'verify-jvm-result!))
(def stages @(ns-resolve 'coherent-bootstrap-result-model 'jvm-stages))
(def summarize-failure (ns-resolve 'coherent-bootstrap-result-model 'failure-summary))
(def approved {:contract-sha256 (apply str (repeat 64 "a"))
               :implementation-sha256 (apply str (repeat 64 "b"))
               :compatibility-profile "ansatz-producer50f-coherent-jvm-application-consumer/1"
               :execution {:backend :mutable :fuel 500000000 :compile-threshold 1}})
(def good-result
  (merge (:execution approved)
         {:status :passed :disposal-phase :disposed :stages stages
          :consumer-contract-sha256 (:contract-sha256 approved)
          :consumer-implementation-sha256 (:implementation-sha256 approved)
          :compatibility-profile (:compatibility-profile approved)
          :application-execution {:backend :jvm :fuel 500000000 :compile-threshold 1}
          :measurements {:corpus [{}] :callback {:loading-effects 0 :invocation-effects 1}
                         :phases (mapv #(hash-map :stage %) stages)}}))

(t/deftest bounded-complete-result-accepted
  (t/is (nil? (verify-result approved good-result))))

(t/deftest stale-incomplete-or-mislabelled-result-rejected
  (doseq [change [(fn [r] (assoc r :extra :unbounded))
                  (fn [r] (dissoc r :consumer-contract-sha256))
                  (fn [r] (assoc r :consumer-contract-sha256 (:implementation-sha256 approved)))
                  (fn [r] (assoc r :consumer-implementation-sha256 (:contract-sha256 approved)))
                  (fn [r] (assoc r :compatibility-profile "old"))
                  (fn [r] (assoc r :status :partial))
                  (fn [r] (assoc r :disposal-phase :running))
                  (fn [r] (assoc r :backend :jvm))
                  (fn [r] (update r :stages pop))
                  (fn [r] (assoc-in r [:stages 8] :project))
                  (fn [r] (assoc-in r [:application-execution :backend] :mutable))
                  (fn [r] (assoc-in r [:measurements :callback :loading-effects] 1))
                  (fn [r] (assoc-in r [:measurements :callback :invocation-effects] 0))
                  (fn [r] (assoc-in r [:measurements :phases 8 :stage] :project))
                  (fn [r] (assoc-in r [:measurements :corpus] []))
                  (fn [r] (assoc-in r [:measurements :corpus] (vec (repeat 5 {}))))]]
    (t/is (thrown? clojure.lang.ExceptionInfo (verify-result approved (change good-result))))))

(t/deftest failure-telemetry-excludes-owner-bearing-data
  (let [owner (Object.)
        result (summarize-failure (ex-info (apply str (repeat 1024 "x")) {:world owner :checkpoint owner}))]
    (t/is (= {:status :failed :error-class "clojure.lang.ExceptionInfo"
              :message (apply str (repeat 512 "x")) :managed-disposal-proven false} result))
    (t/is (not-any? #(identical? owner %) (vals result)))))

(t/run-tests 'coherent-bootstrap-result-test)
