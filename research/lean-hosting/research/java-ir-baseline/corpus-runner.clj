;; From research/lean-hosting; inventory only, never executes guest code.
(load-file "research/unchanged-program-benchmark.clj")
(load-file "research/java-ir-baseline/repl.clj")
(load-file "research/java-ir-baseline/corpus.clj")
(require '[clojure.pprint :as pp])
(let [[artifact output] *command-line-args*
      _ (assert artifact "Pass the separately built Java interpreter jar/directory")
      basis (java-ir-baseline/class-basis artifact)
      result (lean-compatibility-corpus/audit basis "research/compatibility-corpus.edn")]
  (if output
    (spit output (with-out-str (pp/pprint result)))
    (pp/pprint result))
  (shutdown-agents))
