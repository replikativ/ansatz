(ns prototype.nat-tail-benchmark
  "REPL-only measurement of actual exported Nat sum, without Init restore."
  (:require [prototype.nat-tail-execution-test :as fixture]
            [prototype.typed-tail-execution-test :as contract]
            [prototype.block-compile :as block]
            [prototype.lazy-runtime :as lazy]
            [prototype.mutable :as u]
            [prototype.machine :as m]))

(defn measure [f]
  (let [bean ^com.sun.management.ThreadMXBean (java.lang.management.ManagementFactory/getThreadMXBean)
        tid (.threadId (Thread/currentThread))
        _ (when-not (and (.isCurrentThreadCpuTimeSupported bean) (.isThreadCpuTimeEnabled bean)
                         (.isThreadAllocatedMemorySupported bean) (.isThreadAllocatedMemoryEnabled bean))
            (throw (ex-info "Thread CPU/allocation metrics unavailable" {})))
        cpu (.getCurrentThreadCpuTime bean) bytes (.getThreadAllocatedBytes bean tid) wall (System/nanoTime)
        result (f)]
    [result {:cpu-ns (- (.getCurrentThreadCpuTime bean) cpu)
             :wall-ns (- (System/nanoTime) wall)
             :allocated-bytes (- (.getThreadAllocatedBytes bean tid) bytes)}]))

(defn run-experiment
  ([] (run-experiment 10000 3))
  ([n trials]
   (let [input (fixture/input) fs (:runtime input)
         [baseline baseline-prepare] (measure #(lazy/open-program fs {}))
         [compiled tail-prepare] (measure #(lazy/open-program fs (contract/options input)))
         [_ emission] (measure #(block/force-runtime-compilation! compiled))
         start #(contract/start input "sum" [% 0])
         runners {:jvm #(u/freeze (lazy/run! baseline (u/thaw %) 1000000))
                  :nat-region #(u/freeze (lazy/run! compiled (u/thaw %) 1000000))}
         expected (m/run (start n) 1000000)
         [_ promotion] (measure #((:jvm runners) (start 10)))]
     (doseq [_ (range 5) backend [:jvm :nat-region]] ((runners backend) (start 1000)))
     {:schema "nat-tail-benchmark/1" :iterations n :trials trials
      :scope {:prepare "Fresh programs; compiler/Pattern classes already loaded"
              :emission "Shared factory forced outside warm execution"
              :promotion "Generic JVM first n=10 lazy compilation"
              :run "Initial World setup excluded; thaw/run/freeze included; CPU and allocation for current thread"
              :oracle "Full World and carrier shape compared outside measurement"
              :warmup "Five paired n=1000 runs; steady state not established"}
      :compilation {:generic-prepare baseline-prepare :nat-prepare tail-prepare :nat-emission emission :generic-first-promotion promotion}
      :runs (vec (for [trial (range trials) backend (if (even? trial) [:jvm :nat-region] [:nat-region :jvm])]
                   (let [initial (start n) [actual timing] (measure #((runners backend) initial))]
                     (when-not (and (= expected actual)
                                    (= (contract/carrier-shape expected) (contract/carrier-shape actual)))
                       (throw (ex-info "Nat benchmark World mismatch" {:backend backend})))
                     (assoc timing :trial trial :backend backend :result (:result actual) :steps (get-in actual [:stats :steps])))))})))
