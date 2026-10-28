;; One mode per small JVM. Compile research/java/.../PagedRegisters.java into
;; target/paged-register-research/classes and prepend that directory to the
;; experiment classpath. No production classes are replaced or reloaded.
(load-file "research/unchanged-program-benchmark.clj")
(load-file "research/runtime-feasibility.clj")
(load-file "research/paged-registers.clj")
(let [mode (keyword (first *command-line-args*))
      _ (assert (contains? #{:ordinary :adapter-dense :paged-64} mode))
      context (runtime-feasibility/setup)
      run (get-in context [:workloads :mutable-private])
      expected (into {} (for [n [100 300]] [n ((get-in context [:workloads :reference]) n)]))
      probe (fn []
              (doseq [_ (range 40)] (run 100))
              (doseq [_ (range 10)] (run 300))
              {:mode mode :java (System/getProperty "java.version") :clojure (clojure-version)
               :scope "One stable adapter scope per process; private RBMap build/fold/final freeze, no Init."
               :runs (vec (for [n [100 300] trial (range 7)]
                            (let [[actual metrics] (prototype.unchanged-program-benchmark/measure #(run n))]
                              (assert (= (get expected n) actual))
                              (assoc metrics :n n :trial trial))))})]
  (prn (case mode
         :ordinary (probe)
         :adapter-dense (paged-registers/with-runtime Long/MAX_VALUE probe)
         :paged-64 (paged-registers/with-runtime 64 probe))))
