(ns ansatz.tools.verify-profile
  "Wall-clock sampler for imported-store verification.

   This is intentionally lightweight: it samples JVM stack traces while running
   storage/verify-one! over a declaration range, then reports where wall time is
   spent. It is not a replacement for JFR/async-profiler CPU profiles, but it is
   enough to distinguish kernel work from store lookup and verifier mechanics."
  (:require [ansatz.export.storage :as storage]
            [clojure.java.io :as io]
            [clojure.string :as str]))

(defn- usage []
  (println "Usage:")
  (println "  clojure -M -m ansatz.tools.verify-profile <store> <branch> <start> <n> <out-dir> [fuel] [timeout-ms] [sample-ms]")
  (println "  clojure -M -m ansatz.tools.verify-profile seq-window <store> <branch> <warm-n> <n> <out-dir> [fuel] [timeout-ms] [sample-ms]"))

(defn- frame-str [^StackTraceElement f]
  (str (.getClassName f) "/" (.getMethodName f) ":" (.getLineNumber f)))

(defn- category [^StackTraceElement f]
  (let [c (.getClassName f)]
    (cond
      (str/starts-with? c "ansatz.kernel.TypeChecker") :kernel.typechecker
      (str/starts-with? c "ansatz.kernel.Reducer") :kernel.reducer
      (str/starts-with? c "ansatz.kernel.Inductive") :kernel.inductive
      (str/starts-with? c "ansatz.kernel.LeanExprKey") :kernel.expr-key
      (str/starts-with? c "ansatz.kernel.Expr") :kernel.expr
      (str/starts-with? c "ansatz.kernel.EquivManager") :kernel.equiv
      (str/starts-with? c "ansatz.export.storage") :storage
      (str/starts-with? c "konserve.") :storage.konserve
      (str/includes? c "persistent_sorted_set") :storage.pss
      (str/includes? c "fressian") :storage.fressian
      (str/starts-with? c "clojure.") :clojure
      (str/starts-with? c "java.lang.Thread") :threading
      (str/starts-with? c "java.") :java
      (str/starts-with? c "jdk.") :jdk
      :else :other)))

(defn- interesting-frame [frames]
  (or (first
       (remove (fn [^StackTraceElement f]
                 (let [c (.getClassName f)]
                   (or (= c "java.lang.Thread")
                       (str/starts-with? c "java.lang.StackTraceElement")
                       (str/starts-with? c "clojure.lang.AFn"))))
               frames))
      (first frames)))

(defn- owner-frame [frames]
  (or (first
       (filter (fn [^StackTraceElement f]
                 (let [c (.getClassName f)]
                   (or (str/starts-with? c "ansatz.")
                       (str/includes? c "persistent_sorted_set")
                       (str/includes? c "fressian")
                       (str/includes? c "konserve"))))
               frames))
      (interesting-frame frames)))

(defn- stack-signature [frames]
  (->> frames
       (remove (fn [^StackTraceElement f]
                 (= (.getClassName f) "java.lang.Thread")))
       (take 8)
       (map frame-str)
       vec))

(defn- waiting-for-large-stack? [frames]
  (and (some (fn [^StackTraceElement f]
               (and (= "java.lang.Object" (.getClassName f))
                    (str/starts-with? (.getMethodName f) "wait")))
             frames)
       (some (fn [^StackTraceElement f]
               (str/starts-with? (.getClassName f)
                                  "ansatz.export.storage$run_with_large_stack"))
             frames)))

(defn- update-count [m k]
  (update m k (fnil inc 0)))

(defn- top-n [m n]
  (->> m
       (sort-by val >)
       (take n)
       vec))

(defn- sampled-thread? [^Thread t]
  (let [n (.getName t)]
    (or (= n "main")
        (= n "ansatz-large-stack")
        (str/starts-with? n "clojure-agent-send"))))

(defn- start-sampler [interval-ms]
  (let [running? (atom true)
        acc (atom {:samples 0
                   :thread-samples {}
                   :states {}
                   :top-frames {}
                   :categories {}
                   :stacks {}})
        sampler (Thread.
                 (fn []
                   (while @running?
                     (let [all (Thread/getAllStackTraces)]
                       (swap! acc update :samples inc)
                       (doseq [[^Thread t frames] all
                               :when (sampled-thread? t)]
                         (let [thread-name (.getName t)
                               state (str (.getState t))
                               frame (interesting-frame frames)
                               owner (owner-frame frames)
                               fstr (when frame (frame-str frame))
                               cat (cond
                                     (waiting-for-large-stack? frames) :verifier.wait
                                     owner (category owner))
                               sig (stack-signature frames)]
                           (swap! acc update :thread-samples update-count thread-name)
                           (swap! acc update :states update-count [thread-name state])
                           (when fstr
                             (swap! acc update :top-frames update-count [thread-name fstr])
                             (swap! acc update :categories update-count [thread-name cat])
                             (swap! acc update :stacks update-count [thread-name sig])))))
                     (Thread/sleep (long interval-ms))))
                 "ansatz-verify-profile-sampler")]
    (.setDaemon sampler true)
    (.start sampler)
    {:stop (fn []
             (reset! running? false)
             (.join sampler 2000)
             @acc)}))

(defn- add-stats [acc stats]
  (if-not stats
    acc
    (reduce-kv (fn [m k v]
                 (if (number? v)
                   (update m k (fnil + 0) v)
                   m))
               acc
               stats)))

(defn- compact-result [res]
  (-> res
      (dissoc :stats :trace)
      (update :name str)))

(defn- insert-slowest [slowest res limit]
  (->> (conj slowest (compact-result res))
       (sort-by :elapsed-ms >)
       (take limit)
       vec))

(defn- finish-summary!
  ([out sampler t0 store-path branch-name start n completed idx statuses stats-sum
    slowest last-result sample-ms]
   (finish-summary! out sampler t0 store-path branch-name start n completed idx
                    statuses stats-sum slowest last-result sample-ms nil))
  ([out sampler t0 store-path branch-name start n completed idx statuses stats-sum
    slowest last-result sample-ms extra]
  (let [elapsed-ms (/ (- (System/nanoTime) t0) 1e6)
        samples ((:stop sampler))
        summary (merge
                 {:store store-path
                  :branch branch-name
                  :start start
                  :n n
                  :completed completed
                  :idx idx
                  :elapsed-ms elapsed-ms
                  :decls-per-sec (if (pos? elapsed-ms)
                                   (/ (* 1000.0 completed) elapsed-ms)
                                   0.0)
                  :statuses statuses
                  :stats-sum stats-sum
                  :slowest slowest
                  :last-result (some-> last-result compact-result)
                  :sample-ms sample-ms
                  :samples (:samples samples)
                  :thread-samples (:thread-samples samples)
                  :top-states (top-n (:states samples) 30)
                  :top-categories (top-n (:categories samples) 30)
                  :top-frames (top-n (:top-frames samples) 40)
                  :top-stacks (top-n (:stacks samples) 20)}
                 extra)]
    (spit (io/file out "summary.edn") (pr-str summary))
    summary)))

(defn- failed-status? [status]
  (contains? #{:error :fuel-exceeded :missing} status))

(defn- verify-window!
  [ctx n fuel timeout-ms progress-base]
  (loop [i 0
         statuses {}
         stats-sum {}
         slowest []
         last-result nil]
    (if (>= i n)
      {:completed i
       :statuses statuses
       :stats-sum stats-sum
       :slowest slowest
       :last-result last-result}
      (let [res (storage/verify-one! ctx :fuel fuel :timeout-ms timeout-ms)
            status (:status res)
            statuses' (update-count statuses status)
            stats-sum' (add-stats stats-sum (:stats res))
            slowest' (insert-slowest slowest res 25)
            completed (inc i)]
        (when (zero? (mod completed 500))
          (println :progress (+ progress-base completed)
                   :ok (:ok statuses' 0)
                   :errors (+ (:error statuses' 0)
                              (:fuel-exceeded statuses' 0)
                              (:missing statuses' 0))))
        (if (failed-status? status)
          {:completed completed
           :statuses statuses'
           :stats-sum stats-sum'
           :slowest slowest'
           :last-result res}
          (recur completed statuses' stats-sum' slowest' res))))))

(defn profile-range!
  [store-path branch-name start n out-dir fuel timeout-ms sample-ms]
  (let [store (storage/open-store store-path)
        out (io/file out-dir)
        _ (.mkdirs out)
        ctx (storage/prepare-verify store branch-name
                                    :log-file (.getPath (io/file out "verify.log")))
        sampler (start-sampler sample-ms)
        t0 (System/nanoTime)]
    (try
      (storage/skip-to! ctx start)
      (let [{:keys [completed statuses stats-sum slowest last-result]}
            (verify-window! ctx n fuel timeout-ms start)]
        (finish-summary! out sampler t0 store-path branch-name start n completed @(:idx ctx)
                         statuses stats-sum slowest last-result sample-ms))
      (finally
        (try ((:stop sampler)) (catch Throwable _))
        (.close ^java.io.Writer (:log-writer ctx))))))

(defn profile-seq-window!
  "Verify warm-n declarations sequentially without sampling, then profile the
   next n declarations. This approximates full-run behavior better than
   skip-to!, because earlier declarations are already installed in Env."
  [store-path branch-name warm-n n out-dir fuel timeout-ms sample-ms]
  (let [store (storage/open-store store-path)
        out (io/file out-dir)
        _ (.mkdirs out)
        ctx (storage/prepare-verify store branch-name
                                    :log-file (.getPath (io/file out "verify.log")))
        warm-t0 (System/nanoTime)]
    (try
      (dotimes [i warm-n]
        (let [res (storage/verify-one! ctx :fuel fuel :timeout-ms timeout-ms)
              completed (inc i)]
          (when (zero? (mod completed 10000))
            (println :warmup-progress completed
                     :elapsed-ms (/ (- (System/nanoTime) warm-t0) 1e6)))
          (when (failed-status? (:status res))
            (throw (ex-info "Warmup verification failed"
                            {:result (compact-result res)})))))
      (let [warmup-ms (/ (- (System/nanoTime) warm-t0) 1e6)
            sampler (start-sampler sample-ms)
            t0 (System/nanoTime)]
        (try
          (let [{:keys [completed statuses stats-sum slowest last-result]}
                (verify-window! ctx n fuel timeout-ms warm-n)]
            (finish-summary! out sampler t0 store-path branch-name warm-n n completed
                             @(:idx ctx) statuses stats-sum slowest last-result
                             sample-ms {:mode :seq-window
                                        :warm-n warm-n
                                        :warmup-ms warmup-ms}))
          (finally
            (try ((:stop sampler)) (catch Throwable _)))))
      (finally
        (.close ^java.io.Writer (:log-writer ctx))))))

(defn -main [& args]
  (cond
    (= "seq-window" (first args))
    (if (< (count args) 6)
      (usage)
      (let [[_ store branch warm-n n out-dir fuel timeout-ms sample-ms] args
            summary (profile-seq-window! store
                                         branch
                                         (Long/parseLong warm-n)
                                         (Long/parseLong n)
                                         out-dir
                                         (long (if fuel (Long/parseLong fuel) 100000000))
                                         (long (if timeout-ms (Long/parseLong timeout-ms) 600000))
                                         (long (if sample-ms (Long/parseLong sample-ms) 10)))]
        (prn summary)))

    (< (count args) 5)
    (usage)

    :else
    (let [[store branch start n out-dir fuel timeout-ms sample-ms] args
          summary (profile-range! store
                                  branch
                                  (Long/parseLong start)
                                  (Long/parseLong n)
                                  out-dir
                                  (long (if fuel (Long/parseLong fuel) 100000000))
                                  (long (if timeout-ms (Long/parseLong timeout-ms) 600000))
                                  (long (if sample-ms (Long/parseLong sample-ms) 10)))]
      (prn summary))))
