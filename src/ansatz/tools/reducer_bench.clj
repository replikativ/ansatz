(ns ansatz.tools.reducer-bench
  "Small local benchmarks for ansatz.reducers.

   This is intentionally dependency-free. For serious benchmarking, port these
   cases to criterium/jmh; this tool is for quick branch-to-branch comparisons."
  (:refer-clojure :exclude [frequencies])
  (:require [ansatz.reducers :as r]
            [clojure.core.reducers :as reducers])
  (:gen-class))

(defn- parse-long-arg [s default]
  (if s
    (Long/parseLong s)
    default))

(defn- nanos []
  (System/nanoTime))

(defn- elapsed-ms [start stop]
  (/ (double (- stop start)) 1000000.0))

(defn- run-once [f]
  (let [start (nanos)
        ret (f)
        stop (nanos)]
    {:ret ret :ms (elapsed-ms start stop)}))

(defn- bench-case [label f {:keys [warmup runs]}]
  (dotimes [_ warmup] (f))
  (let [samples (doall (repeatedly runs #(run-once f)))
        result (:ret (last samples))
        times (mapv :ms samples)
        total (reduce + times)
        best (apply min times)
        worst (apply max times)]
    {:label label
     :result result
     :runs runs
     :best-ms best
     :avg-ms (/ total runs)
     :worst-ms worst}))

(defn- result-summary [result]
  (if (map? result)
    {:count (count result)
     :hash (hash result)}
    result))

(defn- print-result [{:keys [label result runs best-ms avg-ms worst-ms]}]
  (printf "%-34s result=%s runs=%d best=%.3fms avg=%.3fms worst=%.3fms%n"
          label (pr-str (result-summary result)) runs best-ms avg-ms worst-ms))

(defn run-suite
  "Run reducer benchmarks.

   Options:
     :n       input size, default 1000000
     :runs    measured repetitions, default 8
     :warmup  warmup repetitions, default 3
     :grain   reducers/fold grain, default 8192"
  [{:keys [n runs warmup grain]
    :or {n 1000000 runs 8 warmup 3 grain 8192}}]
  (let [xs (vec (range n))
        pipeline (r/pipeline
                  (map inc)
                  (filter odd?))
        core-xf (comp (map inc) (filter odd?))
        sum-rf (fn
                 ([] 0)
                 ([x] x)
                 ([acc x] (+ acc x)))
        freq-key #(mod % 128)
        freq-rf (fn
                  ([] (transient {}))
                  ([m] (persistent! m))
                  ([m x]
                   (let [k (freq-key x)]
                     (assoc! m k (inc (long (get m k 0)))))))
        cfg {:warmup warmup :runs runs}
        cases [["core/transduce sum"
                #(clojure.core/transduce core-xf sum-rf 0 xs)]
               ["ansatz/transduce sum"
                #(r/transduce pipeline sum-rf 0 xs)]
               ["ansatz/sum-seq"
                #(r/sum-seq pipeline r/nat-add xs)]
               ["ansatz/sum reducers/fold"
                #(r/sum pipeline r/nat-add xs {:grain grain})]
               ["core/reducers fold sum"
                #(->> xs
                      (reducers/map inc)
                      (reducers/filter odd?)
                      (reducers/fold grain + +))]
               ["core/transduce frequencies"
                #(clojure.core/transduce core-xf freq-rf (transient {}) xs)]
               ["ansatz/frequencies-seq"
                #(r/frequencies-seq pipeline r/nat-add freq-key xs)]
               ["ansatz/frequencies fold"
                #(r/frequencies pipeline r/nat-add freq-key xs {:grain grain})]]]
    (println "ansatz.reducer benchmark")
    (println "n=" n "runs=" runs "warmup=" warmup "grain=" grain)
    (doseq [[label f] cases]
      (print-result (bench-case label f cfg)))))

(defn -main [& args]
  (let [[n runs warmup grain] args]
    (run-suite {:n (parse-long-arg n 1000000)
                :runs (parse-long-arg runs 8)
                :warmup (parse-long-arg warmup 3)
                :grain (parse-long-arg grain 8192)})))
