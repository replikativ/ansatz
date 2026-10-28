;; Separate bounded JVM per mode; core prepared runner, no global replacements.
(load-file "research/unchanged-program-benchmark.clj")
(load-file "research/runtime-feasibility.clj")
(require '[prototype.native-call :as native] '[prototype.mutable :as u] '[prototype.machine :as m])
(let [mode (keyword (first *command-line-args*))
      _ (assert (contains? #{:ordinary :driver :fusion :paired} mode))
      modes (if (= :paired mode) [:ordinary :driver :fusion] [mode])
      context (runtime-feasibility/setup)
      [program preparation] (prototype.unchanged-program-benchmark/measure #(native/open-program (:functions context)))
      [mk fold callback] (:names context)
      seed (m/run (m/start (m/world (:functions context)) callback []) 10000)
      runner (fn [mode n]
            (let [s (u/thaw (m/start seed mk [n]))
                  driver (case mode :ordinary u/run! :driver #(native/run! program %1 %2 false nil)
                               :fusion #(native/run! program %1 %2))]
              (driver s 2000000)
              (assert (= :done (u/status s)))
              (u/start! s fold [(:result seed) (aget ^objects (:control s) 5) 0])
              (driver s 2000000)
              (u/freeze s)))
      expected (into {} (for [n [100 300]] [n ((get-in context [:workloads :reference]) n)]))]
  (doseq [_ (range 40) mode modes] (runner mode 100))
  (doseq [_ (range 10) mode modes] (runner mode 300))
  (prn {:mode mode :java (System/getProperty "java.version") :clojure (clojure-version)
        :preparation preparation :wrappers (count (:wrappers program))
        :sites (.size ^java.util.IdentityHashMap (:calls program))
        :runs (vec (for [n [100 300] trial (range 7)
                         mode (if (even? trial) modes (reverse modes))]
                     (let [[actual metrics] (prototype.unchanged-program-benchmark/measure #(runner mode n))]
                       (assert (= (get expected n) actual))
                       (assoc metrics :n n :trial trial :mode mode))))}))
