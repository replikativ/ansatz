(doseq [f ["research/unchanged-program-benchmark.clj"
           "research/java-ir-baseline/repl.clj"
           "research/java-ir-baseline/corpus.clj"
           "research/java-ir-baseline/catalogue.clj"
           "research/java-ir-baseline/kernel-projection.clj"
           "research/java-ir-baseline/source-setup.clj"
           "research/java-ir-baseline/composite-source-v4.clj"
           "research/java-ir-baseline/module-data-graph.clj"
           "research/java-ir-baseline/artifact-frontend/loader.clj"]]
  (binding [*ns* (the-ns 'user)] (load-file f)))
(ansatz.research.ir.artifact-frontend-loader/load!)
(load-file "research/java-ir-baseline/runtime-cohort/loader.clj")
(ansatz.research.ir.runtime-cohort-loader/load!)
(ansatz.research.ir.runtime-cohort-loader/load-models!)
(let [names (mapv second ansatz.research.ir.runtime-cohort-loader/models)
      result (apply clojure.test/run-tests names)]
  (println :packaged-model-results result)
  (shutdown-agents)
  (System/exit (if (and (= 29 (:test result)) (zero? (+ (:fail result) (:error result)))) 0 1)))
