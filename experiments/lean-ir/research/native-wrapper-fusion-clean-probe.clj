;; One mode per bounded JVM; no Init or hosted frontend.
(load-file "research/unchanged-program-benchmark.clj")
(load-file "research/runtime-feasibility.clj")
(load-file "research/prepared-native-ops.clj")
(load-file "research/native-wrapper-fusion.clj")
(let [mode (keyword (first *command-line-args*))
      _ (assert (contains? #{:ordinary :driver :fusion} mode))
      context (runtime-feasibility/setup)
      [program preparation] (prototype.unchanged-program-benchmark/measure
                              #(native-wrapper-fusion/prepare (:functions context)))
      driver (case mode
               :ordinary prototype.mutable/run!
               :driver #(native-wrapper-fusion/run! program %1 %2 false nil)
               :fusion #(native-wrapper-fusion/run! program %1 %2 true nil))
      run (native-wrapper-fusion/workload context driver)
      expected (into {} (for [n [100 300]] [n ((get-in context [:workloads :reference]) n)]))]
  (doseq [_ (range 40)] (run 100))
  (doseq [_ (range 10)] (run 300))
  (prn {:mode mode :java (System/getProperty "java.version") :clojure (clojure-version)
        :preparation preparation :wrappers (count (:wrappers program))
        :sites (.size ^java.util.IdentityHashMap (:calls program))
        :runs (vec (for [n [100 300] trial (range 7)]
                     (let [[actual metrics] (prototype.unchanged-program-benchmark/measure #(run n))]
                       (assert (= (get expected n) actual))
                       (assoc metrics :n n :trial trial))))}))
