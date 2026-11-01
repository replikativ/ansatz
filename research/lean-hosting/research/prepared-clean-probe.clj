;; Run each mode in its own bounded JVM to avoid sharing dispatch profiles.
;; Same resident dependency basis as the REPL; no Init or hosted frontend.
(load-file "research/unchanged-program-benchmark.clj")
(load-file "research/runtime-feasibility.clj")
(load-file "research/interpreter-controls.clj")
(let [mode (keyword (first *command-line-args*))
      _ (assert (contains? #{:ordinary :primitive-driver :prepared} mode))
      _ (when (= mode :prepared)
          (doseq [file ["prepared-interpreter" "prepared-fused"
                        "prepared-native-ops" "prepared-runtime"]]
            (load-file (str "research/" file ".clj"))))
      context (runtime-feasibility/setup)
      program (when (= mode :prepared)
                ((resolve 'prepared-runtime/prepare-program) (:functions context)))
      driver (case mode
               :ordinary prototype.mutable/run!
               :primitive-driver (interpreter-controls/primitive-fuel-run! prototype.mutable/run!)
               :prepared (partial (resolve 'prepared-runtime/run!) program))
      [mk fold callback] (:names context)
      seed (prototype.machine/run
            (prototype.machine/start (prototype.machine/world (:functions context)) callback []) 10000)
      run (fn [n]
            (let [machine (prototype.mutable/thaw (prototype.machine/start seed mk [n]))]
              (driver machine 2000000)
              (assert (= :done (prototype.mutable/status machine)))
              (let [tree (aget ^objects (:control machine) 5)]
                (prototype.mutable/start! machine fold [(:result seed) tree 0]))
              (driver machine 2000000)
              (prototype.mutable/freeze machine)))
      expected (into {} (for [n [100 300]]
                          [n ((get-in context [:workloads :reference]) n)]))]
  (doseq [_ (range 40)] (run 100))
  (doseq [_ (range 10)] (run 300))
  (prn {:mode mode :java (System/getProperty "java.version")
        :clojure (clojure-version)
        :preparation (select-keys program [:preparation-ns :prepared-native-sites])
        :runs (vec (for [n [100 300] trial (range 7)]
                     (let [[actual metrics] (prototype.unchanged-program-benchmark/measure #(run n))]
                       (assert (= (get expected n) actual))
                       (assoc metrics :n n :trial trial))))}))
