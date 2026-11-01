(ns java-entropy-original-random-runners-v1
  (:require [java-ir-baseline] [java-ir-generation-checks] [java-ir-fork-checks]
            [java-entropy-original-random-gate-v1]))
(defn run-original-random-v2! [journal expected-state seed-bytes]
  (let [{:keys [ctx capability] :as prepared} (:prepared @journal)]
    (assert (= :prepared (:status @journal)))
    (try
      (swap! journal assoc :status :opening)
      (let [engine (java-ir-baseline/machine ctx)]
        (swap! journal assoc :engine engine :status :installing)
        (java-entropy-original-random-gate-v1/install! prepared engine)
        (swap! journal assoc :status :initializing)
        (java-entropy-original-random-gate-v1/begin! prepared engine)
        (java-entropy-original-random-gate-v1/drain! prepared engine)
        (let [wrapper (java-ir-generation-checks/field engine "result")
              fields ^java.lang.reflect.Field (:fields ctx)
              payload (aget ^objects (.get fields wrapper) 0)]
          (swap! journal assoc :borrowed-wrapper wrapper :borrowed-payload payload :status :publishing)
          (assert (= 0 (.getInt ^java.lang.reflect.Field (:tag ctx) wrapper)))
          (let [status (java-entropy-original-random-gate-v1/complete! prepared engine)]
            (swap! journal assoc :status-result status :status-result-owned true)
            (assert (= 0 (.getInt ^java.lang.reflect.Field (:tag ctx) status)))
            (java-ir-baseline/release! ctx engine status)
            (swap! journal assoc :status-result-owned false))
          (let [global (java-ir-baseline/call ctx engine "IO.stdGenRef" [])
                generator (aget ^objects (.get fields global) 0)
                state (vec (.get fields generator))
                entropy (java-entropy-original-random-gate-v1/status prepared engine)]
            (assert (identical? payload global))
            (assert (true? (java-ir-generation-checks/field global "ref")))
            (assert (if expected-state (= expected-state state) (and (= 2 (count state)) (<= 1 (first state) 2147483562) (<= 1 (second state) 2147483398))))
            (assert (= 0 (.getInt ^java.lang.reflect.Field (:rc ctx) global)))
            (assert (= 0 (.getInt ^java.lang.reflect.Field (:rc ctx) generator)))
            (assert (true? (java-ir-generation-checks/field wrapper "dead")))
            (assert (= 1 (get entropy "calls")))
            (assert (= 8 (get entropy "bytesRequested")))
            (.invoke (.getMethod ^Class (:class ctx) "finishInitialization" (make-array Class 0)) engine (object-array 0))
            (let [{child :engine roots :roots} (#'java-ir-fork-checks/fork! ctx engine [global])]
              (swap! journal assoc :child child :status :checking-fork)
              (let [child-global (java-ir-baseline/call ctx child "IO.stdGenRef" [])
                    child-state (vec (.get fields (aget ^objects (.get fields child-global) 0)))
                    child-entropy (java-entropy-original-random-gate-v1/status prepared child)
                    draws (.invoke (.getMethod (class capability) "draws" (make-array Class 0)) capability (object-array 0))]
                (assert (identical? (first roots) child-global))
                (assert (not (identical? global child-global)))
                (assert (= state child-state))
                (assert (= 1 (get child-entropy "calls") draws))
                (java-ir-baseline/close! ctx child)
                (java-ir-baseline/close! ctx engine)
                (let [receipt {:status :pass :original-rows 63 :initializer-route :original-raw-void
                               :seed-bytes seed-bytes :stdgen-state state
                               :same-global-payload true :persistent-ref-and-generator true
                               :original-wrapper-consumed true :entropy (into {} entropy)
                               :fork {:ref-copied true :state-copied true :reseeded false :shared-service-draws draws}
                               :parent-closed (java-ir-generation-checks/field engine "closed")
                               :child-closed (java-ir-generation-checks/field child "closed")
                               :full-init-startup false :public-artifact-issuer false}]
                  (reset! journal {:status :closed :prepared prepared :receipt receipt})
                  receipt))))))
      (catch Throwable error
        (swap! journal assoc :status :failed :error error)
        {:status :failed :causes (mapv #(.getMessage %) (take-while some? (iterate ex-cause error)))}))))
