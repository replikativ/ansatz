(ns prototype.typed-tail-preparation-benchmark
  "Optional :typed-tail alias; load in the existing REPL, no process launcher."
  (:require [prototype.typed-tail-test :as fixture]))

(defn samples
  ([] (samples 3))
  ([n]
   (let [input (fixture/bundle "scalar-wrapper-programs.jsonl")
         expected (get-in (fixture/prepare input) [:region :key])
         bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
         thread-id (.threadId (Thread/currentThread))]
     (when-not (and (.isCurrentThreadCpuTimeSupported bean) (.isThreadCpuTimeEnabled bean)
                    (.isThreadAllocatedMemorySupported bean) (.isThreadAllocatedMemoryEnabled bean))
       (throw (ex-info "Thread metrics unavailable" {})))
     (mapv (fn [_]
             (let [cpu (.getCurrentThreadCpuTime bean) allocated (.getThreadAllocatedBytes bean thread-id)
                   wall (System/nanoTime) result (fixture/prepare input)
                   elapsed (- (System/nanoTime) wall)
                   bytes (- (.getThreadAllocatedBytes bean thread-id) allocated)
                   cpu-used (- (.getCurrentThreadCpuTime bean) cpu)
                   region (:region result)]
               ;; Equality/summary traversal is outside the measured interval.
               (assert (= expected (:key region)))
               {:thread-cpu-ns cpu-used :wall-ns elapsed :thread-allocated-bytes bytes
                :status (:status result) :functions (count (:functions region))
                :blocks (reduce + (map (comp count :blocks) (vals (:functions region))))
                :counts (:counts region)})) (range n)))))
