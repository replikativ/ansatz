(ns interpreter-cost-corpus
  "Small resident corpus: phase-separated execution, not hosted file loading."
  (:require [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy]
            [prototype.unchanged-program-benchmark :as benchmark]
            [prepared-runtime :as prepared]
            [prepared-fused :as fused]
            [static-code-dispatch :as static]
            [interpreter-controls :as controls])
  (:import [java.util IdentityHashMap Map$Entry]))

(defn native-only-program [program]
  (let [instructions (IdentityHashMap.)]
    (doseq [^Map$Entry entry (.entrySet ^IdentityHashMap (:instructions program))]
      (when (instance? prepared_runtime.Runtime2SlotConstant (.getValue entry))
        (.put instructions (.getKey entry) (.getValue entry))))
    (assoc program :instructions instructions :scope :native-only)))

(defn runners [context]
  (let [program (prepared/prepare-program (:functions context))
        only (native-only-program program)]
    {:preparation (select-keys program [:preparation-ns :prepared-native-sites :prepared-lets])
     :runs {:ordinary u/run!
            :primitive-driver (controls/primitive-fuel-run! u/run!)
            :prepared (partial prepared/run! program)
            :native-only (partial fused/run! only)
            :compiled (partial lazy/run! (:program context))
            :compiled-static (static/runner (:program context))}}))

(defn probe
  "Each sample separately times a batch of thaw, execution and freeze. All
  final Worlds must equal the reference outside timing. Small workload batch
  amortizes management counter overhead; no guest state crosses executions."
  [context trials batch-size]
  (let [{:keys [runs preparation]} (runners context)
        modes [:ordinary :primitive-driver :prepared :native-only :compiled :compiled-static]]
    {:scope "Original constructor-data roots; raw exported IR, no sampler or frontend execution. Phase counters are per batch; not per-call timings."
     :preparation preparation :batch-size batch-size
     :function-count (count (:functions context))
     :runs
     (vec
      (mapcat
       (fn [entry]
         (let [initial (m/start (m/world (:functions context)) entry [])
               expected (m/run initial 100000)
               _ (assert (= :done (:status expected)))]
           (doseq [_ (range 8) mode modes]
             (assert (= expected (u/freeze ((runs mode) (u/thaw initial) 100000)))))
           (for [trial (range trials)
                 mode (if (even? trial) modes (reverse modes))]
             (let [[machines thaw] (benchmark/measure #(vec (repeatedly batch-size (fn [] (u/thaw initial)))))
                   [_ execution] (benchmark/measure #(doseq [machine machines] ((runs mode) machine 100000)))
                   [worlds freeze] (benchmark/measure #(mapv u/freeze machines))]
               (assert (every? #(= expected %) worlds))
               {:entry entry :trial trial :mode mode
                :guest-stats (:stats expected) :retained-nodes (count (:heap expected))
                :thaw thaw :execution execution :freeze freeze}))))
       (:names context)))}))
