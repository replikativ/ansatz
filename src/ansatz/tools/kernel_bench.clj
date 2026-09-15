(ns ansatz.tools.kernel-bench
  "The kernel's performance harness: a fixed list of declarations checked one at a time from
   the imported store, each reported with wall time, fuel, and the JVM's collector time and
   peak old-generation occupancy — so a kernel change is a number, not an argument.

     clojure -M -m ansatz.tools.kernel-bench run <store> <branch> [decl ...]
     clojure -M -m ansatz.tools.kernel-bench golden <store> <branch> <out-dir> [decl ...]
     clojure -M -m ansatz.tools.kernel-bench compare <dir-a> <dir-b>

   `run` checks the declarations (with -Dansatz.kernel.cacheReport=true each line is followed by
   what the caches held: entries per cache and the nodes they reference by identity and by
   structure) (default: `default-decls`, ordinary heavy declarations plus
   the known outlier localCohomology.diagramComp, which needs a large heap). `golden` writes
   the kernel trace of each declaration into <out-dir> and `compare` matches two such
   directories event for event (ansatz.tools.kernel-trace/compare-traces-semantic): a kernel
   change that only makes checking cheaper leaves the traces identical, so the pair
   golden-before / golden-after is the regression oracle a performance change has to pass.

   Lean's own numbers for the outlier (v4.33.1, profiler): the kernel spends ~123 s on it,
   5.47 M is_def_eq events, and the whole `lean` process peaks at 3.55 GB RSS including the
   imported environment."
  (:require [ansatz.export.storage :as storage]
            [ansatz.tools.kernel-trace :as kt]
            [clojure.java.io :as io]
            [clojure.string :as str]))

(def default-decls
  ["Nat.add_comm"
   "List.map_map"
   "Set.graphOn.eq_1"
   "Rat.instEncodable._proof_3"
   "Std.DTreeMap.Equiv.toArray_eq"
   "Chebyshev.theta_zero"
   "Polynomial.taylorLinearEquiv_symm"
   "CategoryTheory.Limits.PullbackCone.flipIsLimit._proof_3"
   "WittVector.add_coeff_zero"])

(def outlier "localCohomology.diagramComp")

(defn- gc-ms []
  (reduce + 0 (map #(max 0 (.getCollectionTime ^java.lang.management.GarbageCollectorMXBean %))
                   (java.lang.management.ManagementFactory/getGarbageCollectorMXBeans))))

(defn- old-gen-pools []
  (filter #(re-find #"(?i)old|tenured" (.getName ^java.lang.management.MemoryPoolMXBean %))
          (java.lang.management.ManagementFactory/getMemoryPoolMXBeans)))

(defn- reset-peaks! [] (run! #(.resetPeakUsage ^java.lang.management.MemoryPoolMXBean %) (old-gen-pools)))

(defn- peak-old-mb []
  (quot (reduce + 0 (map #(.getUsed (.getPeakUsage ^java.lang.management.MemoryPoolMXBean %)) (old-gen-pools)))
        (* 1024 1024)))

(defn bench-one!
  "Check `decl` in `ctx`; a map of :status :wall-ms :fuel-used :gc-ms :peak-old-mb :error."
  [ctx decl & {:keys [fuel timeout-ms] :or {fuel 1000000000 timeout-ms 900000}}]
  (System/gc)
  (reset-peaks!)
  (set! (. ansatz.kernel.TypeChecker lastCacheReport) nil)
  (let [gc0 (gc-ms) t0 (System/nanoTime)
        r (try (storage/verify-by-name! ctx decl :fuel fuel :timeout-ms timeout-ms)
               (catch Throwable e {:status :error :error (str e)}))]
    ;; a timed-out check leaves its worker computing the cache report; wait for it
    (when (Boolean/getBoolean "ansatz.kernel.cacheReport")
      (loop [n 0]
        (when (and (nil? (. ansatz.kernel.TypeChecker lastCacheReport)) (< n 600))
          (Thread/sleep 500) (recur (inc n)))))
    {:decl decl
     :status (:status r)
     :wall-ms (quot (- (System/nanoTime) t0) 1000000)
     :fuel-used (:fuel-used r)
     :gc-ms (- (gc-ms) gc0)
     :peak-old-mb (peak-old-mb)
     :error (some-> (:error r) str (subs 0 (min 160 (count (str (:error r))))))}))

(defn- open-ctx [store-path branch]
  (let [sm (storage/open-store store-path)]
    [sm (storage/prepare-verify sm branch :log-file "/dev/null")]))

(defn run!*
  [store-path branch decls]
  (let [[sm ctx] (open-ctx store-path branch)]
    (try
      (println (format "%-62s %-8s %9s %12s %8s %8s" "declaration" "status" "wall-ms" "fuel" "gc-ms" "old-MB"))
      (doseq [d decls]
        (let [{:keys [status wall-ms fuel-used gc-ms peak-old-mb error]} (bench-one! ctx d)]
          (println (format "%-62s %-8s %9d %12s %8d %8d %s" d (name (or status :nil)) wall-ms (or fuel-used "-") gc-ms peak-old-mb (or error "")))
          (when-let [r (ansatz.kernel.TypeChecker/lastCacheReport)]
            (println "   caches [entries key-nodes-id key-nodes-struct val-nodes-id val-nodes-struct]:")
            (doseq [[k v] r] (println "     " k (if (instance? (Class/forName "[J") v) (vec v) v))))
          (flush)))
      (finally (storage/close-store sm)))))

(defn golden!
  [store-path branch out-dir decls]
  (let [[sm ctx] (open-ctx store-path branch)]
    (.mkdirs (io/file out-dir))
    (try
      (doseq [d decls]
        (let [out (str out-dir "/" (#'kt/safe-decl-name d) ".jsonl") t0 (System/nanoTime)
              r (try (#'kt/trace-ansatz-ctx! ctx d out 1000000000)
                     (catch Throwable e {:error (str e)}))]
          (println d (or (:events r) (:error r)) (quot (- (System/nanoTime) t0) 1000000) "ms")
          (flush)))
      (finally (storage/close-store sm)))))

(defn compare!
  "Every trace in dir-a against the same-named trace in dir-b; exit 1 on any mismatch."
  [dir-a dir-b]
  (let [files (sort (filter #(str/ends-with? % ".jsonl") (.list (io/file dir-a))))
        results (for [f files]
                  (let [a (str dir-a "/" f) b (str dir-b "/" f)]
                    (if-not (.exists (io/file b))
                      [f :missing]
                      (let [r (kt/compare-traces-semantic a nil b nil 3 2) s (:semantic r)]
                        [f (if (:matched-all? s) :same :differs)
                         (get-in r [:left :events]) (get-in r [:right :events])
                         (when-let [fm (:first-mismatch r)]
                           [(:left-idx fm) (:right-idx fm) (get-in fm [:left :by]) (get-in fm [:right :by])])]))))]
    (doseq [r results] (println (str/join " " (map pr-str r))))
    (if (every? #(= :same (second %)) results) 0 1)))

(defn -main [& [cmd & args]]
  (let [code (case cmd
               "run" (do (run!* (first args) (second args) (or (seq (drop 2 args)) default-decls)) 0)
               "golden" (do (golden! (first args) (second args) (nth args 2) (or (seq (drop 3 args)) default-decls)) 0)
               "compare" (compare! (first args) (second args))
               (do (println "usage: run <store> <branch> [decl ...] | golden <store> <branch> <out-dir> [decl ...] | compare <dir-a> <dir-b>") 2))]
    (shutdown-agents)
    (System/exit code)))
