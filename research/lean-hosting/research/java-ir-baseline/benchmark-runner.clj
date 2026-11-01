;; Warm, bounded execution in one engine. Preparation measured independently.
(load-file "research/unchanged-program-benchmark.clj")
(load-file "research/java-ir-baseline/repl.clj")
(require '[clojure.pprint :as pp])
(let [[artifact output] *command-line-args*
      _ (assert (and artifact output) "Pass engine artifact and output EDN")
      basis (java-ir-baseline/class-basis artifact)
      rows (java-ir-baseline/rows "test/fixtures/unchanged-programs/rbmap.jsonl")
      [program preparation] (prototype.unchanged-program-benchmark/measure
                             #(java-ir-baseline/invoke-static (:prepare basis) [rows]))
      context (assoc basis :program program)
      result (assoc (java-ir-baseline/measure-modes context [300 1000] 100)
                    :preparation preparation :java (System/getProperty "java.version")
                    :clojure (clojure-version) :max-heap (.maxMemory (Runtime/getRuntime)))]
  (spit output (with-out-str (pp/pprint result)))
  (doseq [n [300 1000] mode [:recursive :explicit]
          :let [runs (filter #(and (= n (:n %)) (= mode (:mode %))) (:runs result))
                median #(nth (vec (sort %)) 3)]]
    (println {:n n :mode mode :median-cpu-ms-per-run (/ (median (map :cpu-ns runs)) 1e8)
              :median-wall-ms-per-run (/ (median (map :wall-ns runs)) 1e8)
              :allocated-bytes-per-run (/ (median (map :allocated-bytes runs)) 100.0)}))
  (shutdown-agents))
