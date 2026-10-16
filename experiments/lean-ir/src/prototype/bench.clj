(ns prototype.bench
  (:require [clojure.data.json :as json]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.numeric-compile :as c]
            [prototype.import-ir :as ir])
  (:import [java.lang.management ManagementFactory]
           [com.sun.management ThreadMXBean]))

(defn tail-function [other]
  {:params [0 3]
   :body [:let 1 [:prim :zero? [[:var 0]]]
          [:case [:var 1]
           [[1 [:return [:var 3]]]
            [0 [:let 2 [:prim :dec [[:var 0]]]
                [:let 4 [:prim :inc [[:var 3]]]
                 [:tail [:direct other] [[:var 2] [:var 4]]]]]]]]]})

(defn initial [functions workload n]
  (case workload
    :tail (m/start (m/world {:even (tail-function :odd) :odd (tail-function :even)}) :even [n 0])
    (:unique :shared)
    (let [target (first (filter #(= "List.map._redArg" (ir/name-label %)) (keys functions)))
          [s root] (m/guest-list (m/world functions) (range n))
          s (if (= :shared workload) (m/retain s root 1) s)]
      (m/start s target [(m/->Builtin :inc) root]))))

(def ^ThreadMXBean allocation-bean
  (let [bean (ManagementFactory/getThreadMXBean)]
    (when (and (instance? ThreadMXBean bean) (.isThreadAllocatedMemorySupported ^ThreadMXBean bean))
      (.setThreadAllocatedMemoryEnabled ^ThreadMXBean bean true) bean)))
(defn allocated []
  (when allocation-bean (.getThreadAllocatedBytes allocation-bean (.getId (Thread/currentThread)))))
(defn measure [f]
  (let [allocated-before (allocated) before (System/nanoTime)
        result (f) elapsed (- (System/nanoTime) before)
        bytes (when allocated-before (- (allocated) allocated-before))]
    {:ns elapsed :bytes bytes :value result}))
(defn summarize [measurements]
  (let [times (sort (map :ns measurements)) bytes (sort (keep :bytes measurements))]
    {:samples (count times) :median-ns (nth times (quot (count times) 2))
     :min-ns (first times) :max-ns (last times)
     :median-bytes (when (seq bytes) (nth bytes (quot (count bytes) 2)))
     :raw-ns (vec (map :ns measurements))}))
(defn checksum [workload state]
  (if (= :tail workload) (:result state)
    (first (:fields (m/node state (:result state))))))

(defn execution [functions workload n warmup samples backend]
  (let [snapshot (initial functions workload n)
        prepare (if (= :mutable backend) #(u/thaw snapshot) (constantly snapshot))
        execute (if (= :mutable backend) u/run! m/run)
        finish (if (= :mutable backend) u/freeze identity)
        expected (if (= :tail workload) n 1)]
    (dotimes [_ warmup] (execute (prepare)))
    (let [measurements
          (mapv (fn [_]
                  (let [machine (prepare)
                        measured (measure #(execute machine))
                        state (finish (:value measured))]
                    (when-not (and (= :done (:status state)) (= expected (checksum workload state)))
                      (throw (ex-info "Benchmark result mismatch" {:backend backend :workload workload})))
                    (dissoc measured :value))) (range samples))]
      (merge {:backend backend :workload workload :size n :checksum expected}
             (summarize measurements)))))

(defn checkpoint [functions n warmup samples]
  (let [snapshot (initial functions :unique n)
        machine (u/run! (u/thaw snapshot) 20)
        captured (u/freeze machine)]
    (dotimes [_ warmup] (u/thaw (u/freeze machine)))
    {:size n :live-frames (count (:frames captured)) :live-nodes (count (:heap captured))
     :freeze (summarize (mapv (fn [_] (dissoc (measure #(u/freeze machine)) :value)) (range samples)))
     :restore (summarize (mapv (fn [_] (dissoc (measure #(u/thaw captured)) :value)) (range samples)))}))

(defn compiled [warmup samples]
  (let [functions {:even (tail-function :odd) :odd (tail-function :even)}
        first-compile (measure #(c/compile-program functions))
        invoke (:invoke (:value first-compile))
        compile-samples (mapv (fn [_] (dissoc (measure #(c/compile-program functions)) :value)) (range 5))]
    (dotimes [_ (max 200 warmup)] (invoke :even [20000 0]))
    {:warmup (max 200 warmup) :compile-first-ns (:ns first-compile)
     :compile-repeated (summarize compile-samples)
     :execution (merge {:backend :compiled-numeric :workload :tail :size 20000 :checksum 20000}
                       (summarize (mapv (fn [_]
                                          (let [sample (measure #(invoke :even [20000 0]))]
                                            (when-not (= 20000 (:value sample))
                                              (throw (ex-info "Compiled result mismatch" {})))
                                            (dissoc sample :value))) (range samples))))}))

(defn -main [& [warmup samples]]
  (let [warmup (Long/parseLong (or warmup "20")) samples (Long/parseLong (or samples "11"))
        functions (ir/load-bundle "fixtures/list-map.jsonl")
        results (for [[workload n] [[:tail 20000] [:unique 1000] [:shared 1000]]
                      backend [:persistent :mutable]]
                  (execution functions workload n warmup samples backend))]
    (println (json/write-str
              {:java-version (System/getProperty "java.version")
               :clojure-version (clojure-version) :warmup warmup :samples samples
               :execution (vec results)
               :compiled (compiled warmup samples)
               :checkpoints (mapv #(checkpoint functions % warmup samples) [100 1000 10000])}))
    (shutdown-agents)))
