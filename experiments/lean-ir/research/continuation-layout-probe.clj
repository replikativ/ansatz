(ns continuation-layout-probe
  "Small JVM-only controls; load resident-cost-probe.clj first. No Init, Source
   or genuine frontend. Allocation is per calling thread; assertions are outside
   measurement. Cold sizing uses a fresh cache generation per trial."
  (:require [prototype.raw-interop :as raw] [prototype.machine :as m]
            [prototype.mutable :as u] [prototype.continuation-layout :as layout]
            [resident-cost-probe :as probe]))

(defn run-case [backend kind n samples]
  (assert (contains? #{:reference :mutable :jvm} backend))
  (assert (contains? #{:guest :host} kind))
  (assert (contains? #{1 10 100} n))
  (let [body (reduce (fn [body _]
                       (case kind :guest [:call 2 [:direct "id"] [[:var 1]] body]
                                  :host [:host "ping" [[:var 1]] 2 body]))
                     [:return [:var 1]] (range n))
        functions {"entry" {:params [1] :body body} "id" {:params [1] :body [:return [:var 1]]}}
        bindings {"ping" {:signature {:params [{:ty "uint64" :borrow false}] :return-type "uint64"}
                            :handler (fn [_ world [arg]] [world arg])}}
        session (raw/open-functions functions bindings {:backend backend :compile-threshold 1})
        world (m/world functions) invoke #(raw/call session world "entry" [42])
        thaws (atom 0) freezes (atom 0) thaw u/thaw freeze u/freeze]
    (let [reference (raw/open-functions functions bindings {:backend :reference})
          expected (:state (raw/call reference world "entry" [42]))]
      (dotimes [_ 20] (invoke))
      (let [measurements (mapv (fn [_]
                               (let [[result metrics] (probe/measure invoke)]
                                 (assert (= 42 (:value result)))
                                 (assert (= expected (:state result)))
                                 metrics)) (range samples))
          counted (with-redefs [u/thaw (fn [world] (swap! thaws inc) (thaw world))
                                u/freeze (fn [machine] (swap! freezes inc) (freeze machine))]
                    (invoke))]
      (assert (= 42 (:value counted)))
      {:backend backend :kind kind :calls n :metrics (probe/summarize measurements)
       :steps (get-in counted [:state :stats :steps]) :thaws @thaws :freezes @freezes}))))

(defn run-legacy-case [backend kind n samples]
  ;; Restore the previous sizing path only within this controlled probe.
  (with-redefs [layout/width (fn [body fallback legacy _ _] (legacy body fallback))]
    (run-case backend kind n samples)))

(defn run-size [n samples]
  (assert (contains? #{10 100 300} n))
  (let [roots (reduce (fn [roots _] (conj roots [:host "ping" [[:var 1]] 2 (peek roots)]))
                      [[:return [:var 1]]] (range n))
        roots (vec (rseq roots)) legacy @#'u/measure-continuation-slots expected (mapv #(legacy % 3) roots)
        legacy-run #(mapv (fn [body] (legacy body 3)) roots)
        generation (volatile! (Object.))
        optimized-run #(mapv (fn [body] (layout/width body 3 legacy #'u/builtin-continuation-layout? @generation)) roots)
        measure (fn [f] (let [[widths metrics] (probe/measure f)] (assert (= expected widths)) metrics))]
    {:continuations (count roots)
     :legacy (probe/summarize (mapv (fn [_] (measure legacy-run)) (range samples)))
     :bottom-up-cold (probe/summarize (mapv (fn [_] (vreset! generation (Object.)) (measure optimized-run)) (range samples)))
     :bottom-up-warm (probe/summarize (mapv (fn [_] (measure optimized-run)) (range samples)))}))
