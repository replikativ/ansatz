(ns prototype.typed-tail-benchmark
  "Repeatable optional-Pattern REPL measurement; load after the experiment tests."
  (:require [prototype.typed-tail-test :as fixture]
            [prototype.typed-tail-execution-test :as execution-fixture]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.block-compile :as block]
            [prototype.lazy-runtime :as lazy]))

(defn- measure [f]
  (let [bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        tid (.threadId (Thread/currentThread))
        _ (when-not (and (.isCurrentThreadCpuTimeSupported bean) (.isThreadCpuTimeEnabled bean)
                         (.isThreadAllocatedMemorySupported bean) (.isThreadAllocatedMemoryEnabled bean))
            (throw (ex-info "Thread CPU/allocation metrics unavailable" {})))
        cpu (.getCurrentThreadCpuTime bean) allocation (.getThreadAllocatedBytes bean tid) wall (System/nanoTime)
        value (f)
        elapsed (- (System/nanoTime) wall) used (- (.getThreadAllocatedBytes bean tid) allocation)
        cpu-used (- (.getCurrentThreadCpuTime bean) cpu)]
    [value {:thread-cpu-ns cpu-used :wall-ns elapsed :thread-allocated-bytes used}]))

(defn run-experiment
  ([] (run-experiment 10000 5))
  ([n trials]
   (let [input (fixture/bundle "scalar-wrapper-programs.jsonl") fs (:runtime input)
         [scalar scalar-preparation] (measure #(lazy/open-program fs {:scalar-wrappers (:descriptors input)}))
         [tail tail-preparation] (measure #(lazy/open-program fs (execution-fixture/options input)))
         [_ tail-emission] (measure #(block/force-runtime-compilation! tail))
         runners {:jvm-scalar #(u/freeze (lazy/run! scalar (u/thaw %) 1000000))
                  :jvm-typed-tail #(u/freeze (lazy/run! tail (u/thaw %) 1000000))}
         labels ["sum64" "sumSize"]
         initial #(execution-fixture/start input %1 [%2 0])
         expected (into {} (for [label labels] [label (m/run (initial label n) 1000000)]))
         [_ scalar-promotion] (measure #(doseq [label labels] ((:jvm-scalar runners) (initial label 10))))]
     (doseq [_ (range 8) label labels backend [:jvm-scalar :jvm-typed-tail]]
       ((get runners backend) (initial label 1000)))
     {:schema "typed-tail-experiment/1" :iterations n :trials trials
      :measurement {:prepare "fresh lazy programs; already loaded compiler and Pattern classes"
                    :emit "typed-tail shared group factory forced separately, before warm execution"
                    :scalar-promotion "first scalar tier lazy compilation through n=10 both functions"
                    :execute "paired warmed actual imports, alternating backend order"
                    :setup "initial World construction excluded; thaw/run/freeze included"
                    :warmup-rounds 8 :warmup-iterations 1000 :host-jit-steady-state-established false}
      :compilation {:scalar-prepare scalar-preparation :typed-tail-prepare tail-preparation
                    :typed-tail-emission tail-emission :scalar-first-promotion scalar-promotion}
      :runs (vec (for [trial (range trials) label labels
                       backend (if (even? trial) [:jvm-scalar :jvm-typed-tail] [:jvm-typed-tail :jvm-scalar])]
                   (let [world (initial label n) [actual measured] (measure #((get runners backend) world))]
                     (when-not (= (get expected label) actual)
                       (throw (ex-info "Full benchmark World mismatch" {:backend backend :function label})))
                     (assoc measured :trial trial :function label :backend backend :result (:result actual)
                            :steps (get-in actual [:stats :steps])
                            :logical-allocations (get-in actual [:stats :allocations])))))
      :heap-used (.getUsed (.getHeapMemoryUsage (java.lang.management.ManagementFactory/getMemoryMXBean)))
      :heap-limit (.maxMemory (Runtime/getRuntime))
      :limitations ["Small warmed trials, not sustained host-JIT throughput."
                    "No Source/Init restore or hosted-frontend acceptance."]})))
