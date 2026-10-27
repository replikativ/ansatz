(ns prototype.prefix-retirement-probe
  "Tiny 17-constant fixture; measure closed-branch retirement without Init.
   Load prefix-cost-probe.clj first; its owned fixture builder is reused."
  (:require [prototype.prefix-cost-probe :as fixture-image]
            [prototype.resident-init-prefix-test :as fixture]
            [prototype.resident-init-prefix :as prefix]
            [prototype.resident-frontend :as resident]
            [prototype.machine :as m]))

(defn run-size [n samples]
  (assert (contains? #{0 1000 10000} n))
  (assert (<= 1 samples 20))
  (let [source-cell (volatile! nil)
        result
        (fixture/with-fixture :mutable
          (fn [{:keys [source] :as initial}]
            (vreset! source-cell source)
            (let [owners (atom []) own! (fn [ctx] (swap! owners conj ctx) ctx)
                  grown (#'fixture-image/grow-fixture initial n own!)
                  packet (fixture/prepare grown) context (own! (:context packet))
                  capability (:prefix packet) before (resident/snapshot context)
                  state (:state (first (vals (get-in before [:world :source-import-prefixes]))))
                  close-branch resident/close-prepared-branch!
                  latest (volatile! nil)]
              (try
                (with-redefs [resident/close-prepared-branch!
                              (fn [prepared]
                                (let [world (close-branch prepared)] (vreset! latest world) world))]
                  (let [trials
                        (mapv (fn [_]
                                (let [[closed metrics] (#'fixture-image/measure
                                                         #(prefix/release-prefix-and-close-branch context capability)
                                                         (constantly nil))]
                                  (assert (= :closed (:status closed)))
                                  (assert (= (prefix/descriptor capability) (:receipt closed)))
                                  (assert (empty? (:source-import-prefixes @latest)))
                                  (assert (not (contains? (:heap @latest) (:id state))))
                                  (assert (identical? before (resident/snapshot context)))
                                  (assert (= 1 (:rc (m/node (:world before) state))))
                                  (assert (false? @(:closed source)))
                                  (vreset! latest nil)
                                  metrics)) (range (inc samples)))]
                    {:scope :tiny-source-modeled-helpers-not-Init :synthetic-dependencies n
                     :cold (first trials) :warm-trials (subvec trials 1)
                     :warm-medians (into {} (for [metric [:wall-ns :cpu-ns :allocated-bytes]]
                                             [metric (#'fixture-image/median (map metric (subvec trials 1)))]))}))
                (finally (doseq [ctx (reverse @owners)] (resident/close! ctx)))))))]
    (assert (true? @(:closed @source-cell)))
    (assoc result :source-closed-after-fixture true)))
