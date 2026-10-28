;; Run from experiments/lean-ir with a separately compiled class directory/jar.
;; Neither the engine nor this classpath belongs to normal Ansatz loading.
(load-file "research/unchanged-program-benchmark.clj")
(load-file "research/java-ir-baseline/repl.clj")
(load-file "research/java-ir-baseline/checks.clj")
(let [artifact (first *command-line-args*)
      _ (assert artifact "Pass compiled engine directory or jar")
      basis (java-ir-baseline/class-basis artifact)
      _ (assert (identical? (:loader basis) (.getClassLoader ^Class (:class basis)))
                "Engine must come from the isolated artifact loader")
      _ (when (.endsWith ^String artifact ".jar")
          (assert (= "jar" (.getProtocol (.getResource ^Class (:class basis) "Interpreter.class")))
                  "Expected engine class from jar"))
      result (java-ir-baseline-checks/check! basis)]
  (shutdown-agents)
  (System/exit (if (and (= 9 (:test result)) (zero? (:fail result)) (zero? (:error result))) 0 1)))
