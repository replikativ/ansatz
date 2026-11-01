(ns runtime-feasibility
  "Load unchanged-program-benchmark.clj first in an existing small REPL.
   Raw exported IR only: no hosted frontend, Init, admission or Source."
  (:require [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy])
  (:import [jdk.jfr Recording Configuration]
           [jdk.jfr.consumer RecordingFile]
           [java.nio.file Paths]
           [java.time Duration]))

(defn setup []
  (let [context (prototype.unchanged-program-benchmark/setup
                 "test/fixtures/unchanged-programs/rbmap.jsonl"
                 ["mkMap" "fold._redArg" "main._closed_0"])
        [mk fold callback] (:names context)
        seed (m/run (m/start (m/world (:functions context)) callback []) 10000)
        callback (:result seed)
        initial #(m/start seed mk [%])
        ordinary (fn [backend n]
                   (let [runner (get-in context [:runners backend])
                         tree (runner (initial n) 2000000)]
                     (assert (= :done (:status tree)))
                     (runner (m/start tree fold [callback (:result tree) 0]) 2000000)))
        private-run (fn [backend n]
                      (let [machine (u/thaw (initial n))
                            run! (if (= backend :jvm)
                                   #(lazy/run! (:program context) % 2000000)
                                   #(u/run! % 2000000))]
                        (run! machine)
                        (assert (= :done (aget ^objects (:control machine) 4)))
                        (let [tree (aget ^objects (:control machine) 5)]
                          (u/start! machine fold [callback tree 0]))
                        (run! machine)
                        (u/freeze machine)))]
    (assoc context :initial initial :workloads
           {:reference #(ordinary :reference %)
            :mutable #(ordinary :mutable %)
            :jvm #(ordinary :jvm %)
            :mutable-private #(private-run :mutable %)
            :jvm-private #(private-run :jvm %)})))

(defn clojure-tree [n]
  ;; Platform baseline, not the same red/black implementation or logical RC.
  (let [tree (loop [i (long n) tree (sorted-map)]
               (if (zero? i) tree
                 (let [k (dec i)] (recur k (assoc tree k (zero? (rem k 10)))))))]
    (reduce-kv (fn [total _ value] (if value (inc total) total)) 0 tree)))

(defn java-tree [n]
  ;; Mutable platform baseline; deliberately has no persistent fork guarantee.
  (let [tree (java.util.TreeMap.)]
    (dotimes [i n] (let [k (- n i 1)] (.put tree k (zero? (rem k 10)))))
    (reduce (fn [total value] (if value (inc total) total)) 0 (.values tree))))

(defn clojure-sum [n]
  (loop [i (long n) total (long 0)]
    (if (zero? i) total (recur (unchecked-dec i) (unchecked-add total i)))))

(defn typed-context []
  (let [bundle (ns-resolve 'prototype.typed-tail-test 'bundle)
        options (ns-resolve 'prototype.typed-tail-execution-test 'options)
        start (ns-resolve 'prototype.typed-tail-execution-test 'start)
        input (bundle "scalar-wrapper-programs.jsonl")
        program (lazy/open-program (:runtime input) (options input))]
    {:program program
     :workloads {:typed (fn [n]
                          (u/freeze (lazy/run! program (u/thaw (start input "sum64" [n 0])) 1000000)))}}))

(defn typed-scaling
  "Load typed-tail-benchmark.clj first (optional Pattern). Reuse one prepared
   program to distinguish fixed entry cost from per-loop execution cost."
  ([] (typed-scaling (typed-context)))
  ([context]
  (let [run (get-in context [:workloads :typed])]
    (doseq [_ (range 16)] (run 1000) (clojure-sum 1000))
    {:scope "One retained typed program, preparation excluded; entry checks, initial state, thaw/run/freeze included. Fixed cost distinguished from loop scaling. Small positive longs only."
     :runs
     (vec (for [n [0 10 100 1000 10000 50000] trial (range 7)
                [backend f] [[:typed run] [:clojure clojure-sum]]]
            (let [[actual metrics] (prototype.unchanged-program-benchmark/measure #(f n))
                  value (if (= :typed backend) (:result actual) actual)]
              (when (= :typed backend) (assert (= :done (:status actual))))
              (assert (= (quot (* n (inc n)) 2) value))
              (assoc metrics :n n :trial trial :backend backend))))})))

(defn benchmark [context sizes trials]
  (let [workloads (assoc (:workloads context) :clojure-tree clojure-tree :java-tree java-tree)]
    (doseq [_ (range 8) [_ run] workloads] (run 100))
    {:scope "Preparation excluded; fresh state per trial; eight n100 warmups; paired complete-World parity outside timed interval. Platform trees are different implementations, not Lean speed ratios."
     :runs
     (vec (for [n sizes
                :let [expected ((:reference workloads) n)]
                trial (range trials)
                [backend run] (if (even? trial) workloads (reverse workloads))]
            (let [[actual metrics] (prototype.unchanged-program-benchmark/measure #(run n))
                  platform? (#{:clojure-tree :java-tree} backend)]
              (assert (= (quot (+ n 9) 10) (if platform? actual (:result actual))))
              (when-not platform? (assert (= expected actual)))
              (assoc metrics :n n :trial trial :backend backend
                     :steps (when-not platform? (get-in actual [:stats :steps]))))))
     :compiled (lazy/summary (:program context))}))

(defn profile!
  "One recording for one warmed workload. Weighted allocation/CPU stack samples
   are diagnostic, not exact allocation totals or retained heap. No timing claim."
  [context backend n repetitions path]
  (let [run (get-in context [:workloads backend])
        output (Paths/get path (make-array String 0))
        _ (some-> (.getParent output) .toFile .mkdirs)
        exact (atom nil)
        tid (.threadId (Thread/currentThread))]
    (with-open [recording (Recording. (Configuration/getConfiguration "profile"))]
      (.setMaxSize recording (* 32 1024 1024))
      (.setMaxAge recording (Duration/ofSeconds 30))
      (-> (.enable recording "jdk.ObjectAllocationSample") (.with "throttle" "1000/s") .withStackTrace)
      (-> (.enable recording "jdk.ExecutionSample") (.withPeriod (Duration/ofMillis 2)) .withStackTrace)
      (.start recording)
      (try (reset! exact
                   (second (prototype.unchanged-program-benchmark/measure
                            #(dotimes [_ repetitions] (assert (= :done (:status (run n))))))))
           (finally (.stop recording)))
      (.dump recording output))
    (with-open [file (RecordingFile. output)]
      (loop [result {:allocation-samples 0 :execution-samples 0
                     :exact-profiled-window @exact :allocation-weight-outliers []
                     :allocation-classes {} :allocation-stacks {} :execution-stacks {}}]
        (if-not (.hasMoreEvents file) result
          (let [event (.readEvent file)
                kind (.getName (.getEventType event))
                allocation? (= kind "jdk.ObjectAllocationSample")
                execution? (= kind "jdk.ExecutionSample")
                thread (cond allocation? (.getThread event)
                             execution? (.getThread event "sampledThread"))]
            (if-not (and thread (= tid (.getJavaThreadId thread)) (or allocation? execution?))
              (recur result)
              (let [frames (some-> event .getStackTrace .getFrames)
                    stack (vec (take 12 (map (fn [frame]
                                              (let [method (.getMethod frame)]
                                                (str (.getName (.getType method)) "/" (.getName method))))
                                            frames)))]
                (recur
                 (if allocation?
                   (let [weight (.getLong event "weight")
                         cls (.getName (.getClass event "objectClass"))]
                     ;; A sample exceeding the entire measured allocation
                     ;; window cannot be attributed to this workload. Preserve
                     ;; it separately rather than publish a false percentage.
                     (if (> weight (:allocated-bytes @exact))
                       (update result :allocation-weight-outliers conj {:weight weight :class cls :stack stack})
                       (-> result (update :allocation-samples inc)
                           (update-in [:allocation-classes cls] (fnil + 0) weight)
                           (update-in [:allocation-stacks stack] (fnil + 0) weight))))
                   (-> result (update :execution-samples inc)
                       (update-in [:execution-stacks stack] (fnil inc 0)))))))))))))
