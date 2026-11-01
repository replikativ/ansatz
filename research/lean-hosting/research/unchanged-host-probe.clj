(ns unchanged-host-probe
  "Explicit scalar callbacks only, no Init/Source/frontend. Load
   resident-cost-probe.clj first. Assertions/counters run outside measurement."
  (:require [prototype.raw-interop :as raw] [prototype.machine :as m]
            [resident-cost-probe :as measure]))
(defn run-size [backend n samples]
  (assert (contains? #{:mutable :jvm} backend))
  (assert (contains? #{1 10 100} n))
  (assert (<= 1 samples 100))
  (let [body (reduce (fn [body _] [:host "ping" [[:var 1]] 2 body]) [:return [:var 2]] (range n))
        functions {"entry" {:params [1] :body body}}
        bindings {"ping" {:signature {:params [{:ty "uint64" :borrow false}] :return-type "uint64"}
                          :handler (fn [_ world [x]] [world x])}}
        session (raw/open-functions functions bindings {:backend backend :compile-threshold 1})
        reference (raw/open-functions functions bindings {:backend :reference})
        world (m/world functions) expected (:state (raw/call reference world "entry" [42]))
        invoke #(raw/call session world "entry" [42])
        lane (fn []
               (dotimes [_ 20] (invoke))
               (let [trials (mapv (fn [_]
                                    (let [[result metrics] (measure/measure invoke)]
                                      (assert (= expected (:state result))) metrics)) (range samples))
                     counters (long-array 4)
                     result (with-bindings {#'raw/*boundary-counts* counters} (invoke))]
                 (assert (= expected (:state result)))
                 {:metrics (measure/summarize trials)
                  :counts (zipmap [:restores :reuses :freezes :reference-runs] (vec counters))}))
        runner @#'raw/run-boundary
        baseline (with-redefs-fn {#'raw/run-boundary (fn [s w f] (runner s w f))} lane)
        optimized (lane)]
    (assert (= (inc n) (get-in baseline [:counts :restores])))
    (assert (= 1 (get-in optimized [:counts :restores])))
    (assert (= n (get-in optimized [:counts :reuses])))
    (assert (= (inc n) (get-in optimized [:counts :freezes])))
    {:backend backend :host-calls n :scope :explicit-scalar-identity-callbacks
     :baseline baseline :optimized optimized}))
