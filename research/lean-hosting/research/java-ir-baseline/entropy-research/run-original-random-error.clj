(ns java-entropy-original-random-runners-v1
  (:require [java-ir-baseline] [java-ir-generation-checks] [java-ir-fork-checks]
            [java-entropy-original-random-gate-v1]))
(defn run-original-random-error-v1! [journal]
  (let [{:keys [ctx capability] :as p} (:prepared @journal)]
    (try
      (let [engine (java-ir-baseline/machine ctx)]
        (swap! journal assoc :engine engine :status :installing)
        (java-entropy-original-random-gate-v1/install! p engine)
        (java-entropy-original-random-gate-v1/begin! p engine)
        (java-entropy-original-random-gate-v1/drain! p engine)
        (let [wrapper (java-ir-generation-checks/field engine "result")
              fields ^java.lang.reflect.Field (:fields ctx)
              value (aget ^objects (.get fields wrapper) 0)
              message (aget ^objects (.get fields value) 0)]
          (swap! journal assoc :borrowed-wrapper wrapper :status :completing-error)
          (assert (= 1 (.getInt ^java.lang.reflect.Field (:tag ctx) wrapper)))
          (assert (= 18 (.getInt ^java.lang.reflect.Field (:tag ctx) value)))
          (assert (= "JDK entropy source failed: controlled expected source failure" message))
          (let [returned (java-entropy-original-random-gate-v1/complete! p engine)]
            (swap! journal assoc :owned-error returned)
            (assert (identical? wrapper returned))
            (assert (false? (aget ^booleans (java-ir-generation-checks/field engine "constantReady")
                                         (java-ir-baseline/function-id ctx "IO.stdGenRef"))))
            (assert (java-ir-generation-checks/bad?
                     #(.invoke (.getMethod ^Class (:class ctx) "finishInitialization" (make-array Class 0))
                               engine (object-array 0))))
            (assert (java-ir-generation-checks/bad? #(#'java-ir-fork-checks/fork! ctx engine [])))
            (assert (java-ir-generation-checks/bad? #(java-entropy-original-random-gate-v1/begin! p engine)))
            (let [status (into {} (java-entropy-original-random-gate-v1/status p engine))
                  draws (.invoke (.getMethod (class capability) "draws" (make-array Class 0)) capability (object-array 0))]
              (assert (= 1 draws (get status "calls")))
              (java-ir-baseline/release! ctx engine returned)
              (swap! journal dissoc :owned-error)
              (java-ir-baseline/close! ctx engine)
              (let [receipt {:status :pass :original-rows 63 :initializer-route :original-raw-void
                             :actual-io-error-user-error true :message message :same-error-wrapper true
                             :global-unpublished true :startup-finish-refused true :fork-refused true
                             :retry-refused true :entropy status :source-draws draws
                             :known-error-owner-released true :engine-closed true :full-init-startup false}]
                (reset! journal {:status :closed :prepared p :receipt receipt})
                receipt)))))
      (catch Throwable error
        (swap! journal assoc :status :failed :error error)
        {:status :failed :causes (mapv #(.getMessage %) (take-while some? (iterate ex-cause error)))}))))
