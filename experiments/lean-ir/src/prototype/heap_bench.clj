(ns prototype.heap-bench
  (:require [clojure.data.json :as json]
            [prototype.bench :as stats]
            [prototype.block-compile :as b]
            [prototype.heap-examples :as h]
            [prototype.machine :as m]
            [prototype.mutable :as u]))

(defn cases []
  (for [workload [:map :fold :reverse :mirror] shared? [false true]]
    {:workload workload :size (if (= :mirror workload) 9 1000) :shared? shared?}))

(defn prepare [functions {:keys [workload size shared?]}]
  (if (= :mirror workload) (h/prepare-tree functions size shared?)
      (h/prepare functions workload (range size) shared?)))

(defn execution [functions program scenario backend warmup samples]
  (let [{:keys [initial]} (prepare functions scenario)
        reference (m/run initial)
        setup (if (= :persistent backend) (constantly initial) #(u/thaw initial))
        execute (case backend :persistent m/run :mutable u/run! (:blocks :direct-blocks) #(b/run! program %))
        finish (if (= :persistent backend) identity u/freeze)]
    (dotimes [_ warmup] (execute (setup)))
    (merge scenario {:backend backend :guest-stats (:stats reference)}
           (stats/summarize
            (mapv (fn [_]
                    (let [machine (setup) measured (stats/measure #(execute machine))
                          result (finish (:value measured))]
                      (when-not (= reference result)
                        (throw (ex-info "Heap benchmark differs from reference" {:case scenario :backend backend})))
                      (dissoc measured :value))) (range samples))))))

(defn safepoint [functions program size warmup samples]
  (let [{:keys [initial]} (h/prepare functions :map (range size) false)
        machine (b/run! program (u/thaw initial) 20)
        captured (u/freeze machine)
        freeze #(u/freeze machine) restore #(u/thaw captured)]
    (dotimes [_ warmup] (restore) (freeze))
    {:size size :live-frames (count (:frames captured)) :live-nodes (count (:heap captured))
     :freeze (stats/summarize (mapv (fn [_] (dissoc (stats/measure freeze) :value)) (range samples)))
     :restore (stats/summarize (mapv (fn [_] (dissoc (stats/measure restore) :value)) (range samples)))}))

(defn edit-turnaround [functions program samples]
  (let [edited (assoc-in functions [::h/inc :body] [:let 1 [:prim :dec [[:var 0]]] [:return [:var 1]]])
        initial (:initial (h/prepare edited :map [1 2 3 4] false true))
        measurements
        (mapv (fn [_]
                (let [sample (stats/measure #(let [code (b/compile-program edited program)
                                                  result (u/freeze (b/run! code (u/thaw initial)))]
                                              {:code code :values (m/list-values result (:result result))}))
                      {:keys [code values]} (:value sample)]
                  (when-not (= [0 1 2 3] values) (throw (ex-info "Edited result mismatch" {})))
                  (assoc (dissoc sample :value) :compiled (:compiled-blocks code) :reused (:reused-blocks code))))
              (range samples))]
    {:compile-and-run (stats/summarize measurements)
     :compiled-blocks (:compiled (first measurements)) :reused-blocks (:reused (first measurements))
     :includes [:guest-block-compilation :restore :execution :freeze :result-inspection]
     :excludes [:lean-parsing :lean-elaboration :kernel-admission :ir-export]}))

(defn -main [& [warmup samples]]
  (let [warmup (Long/parseLong (or warmup "20")) samples (Long/parseLong (or samples "11"))
        functions (h/functions)
        first-compile (stats/measure #(b/compile-program functions))
        program (:value first-compile)
        direct-compile (stats/measure #(binding [*compiler-options* (assoc *compiler-options* :direct-linking true)]
                                         (b/compile-program functions)))
        direct (:value direct-compile)
        repeated (mapv (fn [_] (dissoc (stats/measure #(b/compile-program functions)) :value)) (range 3))]
    (println
     (json/write-str
      {:java-version (System/getProperty "java.version") :clojure-version (clojure-version)
       :java-vendor (System/getProperty "java.vendor") :java-vm-version (System/getProperty "java.vm.version")
       :warmup warmup :samples samples :functions (count functions) :blocks (count (:blocks program))
       :compile-first-ns (:ns first-compile) :compile-repeated (stats/summarize repeated)
       :direct-compile-ns (:ns direct-compile)
       :edit-turnaround (edit-turnaround functions program samples)
       :execution (vec (for [case (cases) backend [:persistent :mutable :blocks :direct-blocks]]
                         (execution functions (if (= :direct-blocks backend) direct program)
                                    case backend warmup samples)))
       :safepoints (mapv #(safepoint functions program % warmup samples) [100 1000 10000])}))
    (shutdown-agents)))
