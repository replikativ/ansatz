(ns prototype.scalar-wrapper-benchmark
  "Manual small-REPL experiment over actual exported Lean arithmetic programs."
  (:require [prototype.scalar-wrapper-test :as fixture]
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
   (let [fs @fixture/imported-functions options @fixture/imported-options
         [generic-compiled generic-compilation] (measure #(block/compile-program fs nil {}))
         [scalar-compiled scalar-compilation] (measure #(block/compile-program fs nil options))
         generic (lazy/open-program fs) specialized (lazy/open-program fs options)
         runners {:reference #(m/run % 10000000)
                  :mutable #(u/freeze (u/run! (u/thaw %) 10000000))
                  :jvm-generic #(u/freeze (lazy/run! generic (u/thaw %) 10000000))
                  :jvm-scalar #(u/freeze (lazy/run! specialized (u/thaw %) 10000000))}
         labels ["sum64" "sumSize"]
         start (fn [label n] (m/start (m/world fs) (fixture/imported-target label) [n 0]))
         expected (into {} (for [label labels] [label (m/run (start label n) 10000000)]))]
     ;; Compile/promote the lazy entries, then warm each backend on the same
     ;; actual code. This does not establish host-JIT steady state.
     (doseq [_ (range 12) label labels backend [:reference :mutable :jvm-generic :jvm-scalar]]
       ((get runners backend) (start label 1000)))
     {:schema "scalar-wrapper-experiment/1" :iterations n :trials trials
      :measurement {:compile "fresh eager plans, already loaded compiler classes; one generic-then-scalar sample"
                    :execute "paired warmed actual imported programs, alternating backend order"
                    :setup "initial persistent World construction excluded; thaw/run/freeze included for mutable/JVM"
                    :warmup-rounds 12 :warmup-iterations 1000 :host-jit-steady-state-established false}
      :compilation {:generic-eager generic-compilation :scalar-eager scalar-compilation
                    :generic-blocks (:compiled-blocks generic-compiled) :scalar-blocks (:compiled-blocks scalar-compiled)}
      :runs (vec (for [trial (range trials) label labels
                       backend (if (even? trial) [:reference :mutable :jvm-generic :jvm-scalar]
                                   [:jvm-scalar :jvm-generic :mutable :reference])]
                   (let [initial (start label n) [result measured] (measure #((get runners backend) initial))]
                     (when-not (and (= (quot (*' n (inc n)) 2) (:result result))
                                    (= (get expected label) result))
                       (throw (ex-info "Benchmark full World mismatch" {:backend backend :function label})))
                     (assoc measured :trial trial :function label :backend backend :result (:result result)
                            :steps (get-in result [:stats :steps]) :logical-allocations (get-in result [:stats :allocations])))))
      :heap-used (.getUsed (.getHeapMemoryUsage (java.lang.management.ManagementFactory/getMemoryMXBean)))
      :heap-limit (.maxMemory (Runtime/getRuntime))
      :limitations ["Thread CPU and allocated bytes are host metrics; no sustained throughput claim."
                    "Wrapper-let specialization retains guest calls, returns, generic equality and frame allocations."
                    "No full Init/Source restore, no hosted frontend acceptance."]})))
