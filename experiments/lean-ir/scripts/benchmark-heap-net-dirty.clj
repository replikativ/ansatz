(require '[clojure.test :as t]
         '[clojure.data.json :as json]
         '[prototype.heap-overlay :as overlay]
         '[prototype.machine :as m]
         '[prototype.mutable :as u]
         'prototype.heap-overlay-test
         'prototype.mutable-field-cow-test
         'prototype.mutable-test
         'prototype.native-runtime-test)
(import '[ansatz.runtime HistoricalHeapOverlay]
        '[java.util HashSet])
(let [test-result (t/run-tests 'prototype.heap-overlay-test 'prototype.mutable-field-cow-test
                               'prototype.mutable-test 'prototype.native-runtime-test)]
  (when (pos? (+ (:fail test-result) (:error test-result)))
    (shutdown-agents) (System/exit 1)))

(def historical
  (fn ([base] (HistoricalHeapOverlay. base (HashSet.)))
      ([base dirty] (HistoricalHeapOverlay. base dirty))
      ([base dirty canonical?] (HistoricalHeapOverlay. base dirty canonical?))))
(def candidate overlay/overlay)
(def base-count 16384)
(def ephemeral-count 32768)
(def functions {"read" {:params [0] :body [:let 1 [:project [:var 0] 0] [:return [:var 1]]]}})
(def base (reduce (fn [world i] (first (m/allocate world :ctor 0 [i])))
                  (m/world functions) (range base-count)))
(def first-ref (m/->Ref 0))
;; Establish legitimate storage hints outside timing. No authority is created.
(u/freeze (u/thaw base))
(def bean (java.lang.management.ManagementFactory/getThreadMXBean))
(def thread-id (.getId (Thread/currentThread)))
(def allocated-supported?
  (and (instance? com.sun.management.ThreadMXBean bean)
       (.isThreadAllocatedMemorySupported ^com.sun.management.ThreadMXBean bean)))
(when allocated-supported?
  (.setThreadAllocatedMemoryEnabled ^com.sun.management.ThreadMXBean bean true))
(defn allocated []
  (when allocated-supported? (.getThreadAllocatedBytes ^com.sun.management.ThreadMXBean bean thread-id)))
(defn measured [f]
  (let [a (allocated) t (System/nanoTime) value (f) end (System/nanoTime) b (allocated)]
    {:value value :wall-ms (/ (- end t) 1000000.0)
     :thread-allocated-bytes (when a (- b a))}))
(defn workload [factory mode]
  (with-redefs [overlay/overlay factory]
    (let [state (u/thaw base)
          alloc (measured #(dotimes [i ephemeral-count]
                             (let [r (u/constructor! state 0 [i])]
                               (u/release! state r 1))))
          dirty-before-freeze (.size ^HashSet (:heap-dirty state))
          freeze (measured #(u/freeze state))
          frozen (:value freeze)]
      (assert (= (:heap base) (:heap frozen)))
      (assert (= (+ (:next-id base) ephemeral-count) (:next-id frozen)))
      (assert (= (+ (get-in base [:stats :allocations]) ephemeral-count)
                 (get-in frozen [:stats :allocations])))
      (assert (= 0 (:result (m/run (m/start base "read" [first-ref])))))
      (assert (= 0 (:result (m/run (m/start frozen "read" [first-ref])))))
      (assert (= (if (= mode :candidate) 0 ephemeral-count) dirty-before-freeze))
      (assert (= (= mode :candidate) (identical? (:heap base) (:heap frozen))))
      {:alloc-free (dissoc alloc :value) :freeze (dissoc freeze :value)
       :dirty-before-freeze dirty-before-freeze :frozen-heap-count (count (:heap frozen))
       :reused-exact-base (identical? (:heap base) (:heap frozen))
       :next-id (:next-id frozen) :allocations (get-in frozen [:stats :allocations])
       :old-and-frozen-result 0})))
(def warmups (mapv (fn [_] {:historical (workload historical :historical)
                            :candidate (workload candidate :candidate)}) (range 2)))
(def samples
  (mapv (fn [i]
          (let [order (if (even? i) [:historical :candidate] [:candidate :historical])]
            {:index i :order order
             :results (into {} (for [mode order]
                                 [mode (workload ({:historical historical :candidate candidate} mode) mode)]))}))
        (range 5)))
(spit "target/heap-net-dirty-benchmark.json"
      (json/write-str {:schema "heap-net-dirty-paired-microbenchmark/1"
                       :base-nodes base-count :ephemeral-allocations-per-sample ephemeral-count
                       :warmups warmups :samples samples
                       :allocated-byte-support allocated-supported?
                       :scope "Bounded actual mutable constructor/release/freeze micro workload only; no frontend/campaign speed or retained-byte dominance claim."}))
(println (json/write-str {:event "heap-net-dirty-benchmark-complete" :pairs (count samples)
                          :base-nodes base-count :ephemeral-allocations ephemeral-count}))
(shutdown-agents)
