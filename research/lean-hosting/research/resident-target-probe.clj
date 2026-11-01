(ns resident-target-probe
  "Captured identity IR with synthetic authority dependencies, not guest calls.
   Load resident-cost-probe.clj first. No Init or genuine frontend execution."
  (:require [resident-cost-probe :as probe]
            [prototype.resident-frontend :as resident]
            [prototype.resident-frontend-test :as fixture]
            [prototype.hosted-file-test :as hosted]
            [prototype.raw-interop :as raw]))
(defn run-size [n samples]
  (assert (contains? #{0 1000 10000} n))
  (assert (and (integer? samples) (<= 1 samples 200)))
  (let [base (probe/image 0 false) loaded (fixture/load-identity base) initial (:context loaded)
        data @(.-state ^prototype.resident_frontend.Context initial)
        prepared (:prepared data)
        [target] (#'resident/target! prepared (:file loaded) hosted/answer-name)
        extras (into {} (for [i (range n)] [(str "TargetCost" i) {:params [] :body [:return [:imm 0]]}]))
        changed (assoc (get-in prepared [:world :functions target]) :runtime-dependencies (vec (keys extras)))
        functions (assoc (into (get-in prepared [:world :functions]) extras) target changed)
        registry (assoc (into (get-in prepared [:world :eval-const-authorizations :functions]) extras) target changed)
        prepared (-> prepared (assoc-in [:world :functions] functions)
                     (assoc-in [:world :eval-const-authorizations :functions] registry)
                     (assoc :session (raw/open-functions functions (get-in prepared [:session :bindings])
                                                        (raw/session-options (:session prepared)))))
        context (#'resident/make-context (assoc data :prepared prepared))
        invoke (fn []
                 (let [[result metrics] (probe/measure #(resident/call context (:file loaded) hosted/answer-name [nil 42] fixture/identity-signature))]
                   (assert (= 42 (:value result)))
                   (resident/close! (:context result))
                   metrics))]
    (try
      (let [cold (invoke)]
        (dotimes [_ 5] (invoke))
        {:synthetic-target-dependencies n :cold cold :warm (probe/summarize (mapv (fn [_] (invoke)) (range samples)))})
      (finally (doseq [ctx [context initial base]] (resident/close! ctx))))))
