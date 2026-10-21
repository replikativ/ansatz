(require '[clojure.test :as t]
         '[clojure.data.json :as json]
         '[prototype.mutable :as u]
         '[prototype.machine :as m]
         '[prototype.runtime-prim :as runtime]
         'prototype.runtime-ops-table-test
         'prototype.runtime-prim-test
         'prototype.runtime-array-set-test
         'prototype.native-runtime-test
         'prototype.runtime-integer-test
         'prototype.raw-boundary-test
         'prototype.raw-interop-test
         'prototype.runtime-io-test
         'prototype.runtime-heartbeat-test
         'prototype.runtime-thunk-test
         'prototype.runtime-task-test)
(let [directory (java.io.File. "target")]
  (.mkdirs directory)
  (when-not (.isDirectory directory)
    (throw (ex-info "Benchmark output directory is unavailable" {}))))
(def test-result
  (t/run-tests 'prototype.runtime-ops-table-test 'prototype.runtime-prim-test
               'prototype.runtime-array-set-test 'prototype.native-runtime-test
               'prototype.runtime-integer-test 'prototype.raw-boundary-test
               'prototype.raw-interop-test 'prototype.runtime-io-test
               'prototype.runtime-heartbeat-test 'prototype.runtime-thunk-test
               'prototype.runtime-task-test))
(when (pos? (+ (:fail test-result) (:error test-result)))
  (shutdown-agents) (System/exit 1))

;; The exact 17b43e3 runtime-value! form, renamed only, is evaluated in THIS
;; isolated benchmark JVM. No running frontend/frozen application is changed.
(binding [*ns* (the-ns 'prototype.mutable)]
  (load-file "scripts/benchmarks/runtime-ops-baseline.clj"))
(def baseline (var-get (ns-resolve 'prototype.mutable 'benchmark-baseline-runtime-value!)))
(def candidate u/runtime-value!)
(def world-and-array (m/allocate (m/world {}) :array 246 [7]))
(def machine (u/thaw (first world-and-array)))
(def array-args [m/erased (second world-and-array) 0 m/erased])
(def nat-args [41 1])
(def unicode-args ["λ🦉"])
(def usize-args [0])
(def bean (java.lang.management.ManagementFactory/getThreadMXBean))
(def thread-id (.getId (Thread/currentThread)))
(def allocated-supported?
  (and (instance? com.sun.management.ThreadMXBean bean)
       (.isThreadAllocatedMemorySupported ^com.sun.management.ThreadMXBean bean)))
(when allocated-supported?
  (.setThreadAllocatedMemoryEnabled ^com.sun.management.ThreadMXBean bean true))
(defn allocated []
  (when allocated-supported? (.getThreadAllocatedBytes ^com.sun.management.ThreadMXBean bean thread-id)))
(defn batch [f iterations]
  (let [bytes-before (allocated) started (System/nanoTime)
        checksum
        (loop [i 0 total 0]
          (if (= i iterations) total
            (recur (inc i)
                   (+ total
                      (long (f machine "lean_nat_add" nat-args))
                      (long (f machine "lean_string_length" unicode-args))
                      (long (f machine "lean_array_uget_borrowed" array-args))
                      (long (f machine "lean_get_usize_size" usize-args))))))
        elapsed (- (System/nanoTime) started)
        bytes-after (allocated)]
    (when-not (= checksum (* 59 iterations)) (throw (ex-info "micro checksum mismatch" {})))
    {:iterations iterations :primitive-calls (* 4 iterations) :checksum checksum
     :wall-ms (/ elapsed 1000000.0)
     :thread-allocated-bytes (when bytes-before (- bytes-after bytes-before))}))
(def warmups
  (mapv (fn [i] {:baseline (batch baseline 10000) :candidate (batch candidate 10000)}) (range 5)))
(def samples
  (mapv (fn [i]
          (let [order (if (even? i) [:baseline :candidate] [:candidate :baseline])]
            {:index i :order order
             :results (into {} (map (fn [mode] [mode (batch ({:baseline baseline :candidate candidate} mode) 25000)]) order))}))
        (range 7)))
(defn identities [f]
  (let [seen (java.util.IdentityHashMap.) evaluate runtime/evaluate]
    (with-redefs [runtime/evaluate (fn [ops world symbol args]
                                   (.put seen ops true) (evaluate ops world symbol args))]
      (dotimes [_ 10] (f machine "lean_nat_add" nat-args)))
    (.size seen)))
(defn median [values] (nth (vec (sort values)) (quot (count values) 2)))
(def report
  {:scope "isolated-primitive-ops-table-microbenchmark/1"
   :test-result (select-keys test-result [:test :pass :fail :error])
   :workload ["Nat.add41+1" "String.length Unicodeλ🦉" "borrowedArrayRead[7]" "pinnedusizeQuery"]
   :warmups warmups :measured samples
   :summary (into {} (for [mode [:baseline :candidate]]
                      [mode {:median-wall-ms (median (map #(get-in % [:results mode :wall-ms]) samples))
                             :median-thread-allocated-bytes (when allocated-supported?
                                                              (median (map #(get-in % [:results mode :thread-allocated-bytes]) samples)))}]))
   :ops-map-identities-per10calls {:baseline (identities baseline) :candidate (identities candidate)}
   :before-heap-node-count (count (:heap (first world-and-array)))
   :after-heap-node-count (count (:heap (u/freeze machine)))
   :limits ["Microbenchmark actual primitive evaluation only; no frontend/edit-loop/import/native speed claim."
            "Baseline source is exact 17b43e3 function with name change only; both paths use identical current helpers in same bounded JVM."
            "Five warmups then seven alternating-order paired trials; raw samples retained; allocation counter is current Java thread only."
            "Identity interception is a separate untimed10-call check; timed trials have no runtime/evaluate wrapper."
            "No JVM GC forcing, initializer replay, source/checker change, native compiler or live source reload."]})
(.mkdirs (java.io.File. "target"))
(spit "target/runtime-ops-benchmark.json" (json/write-str report :escape-slash false))
(println (json/write-str (select-keys report [:summary :ops-map-identities-per10calls :test-result])))
(shutdown-agents)
(System/exit 0)
