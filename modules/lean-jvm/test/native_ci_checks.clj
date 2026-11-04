(require '[clojure.data.json :as json]
         '[clojure.java.io :as io]
         '[lake-acceptance :as acceptance]
         '[lake-corpus :as corpus])

;; Exercise the packaged runtime/preparation code, not source or target/classes.
(doseq [resource ["ansatz/lean/jvm.clj" "ansatz/lean/jvm/compiler/workspace.clj"
                  "ansatz/lean/jvm/compiler/evidence.clj" "ansatz/lean/jvm/artifact.clj"]]
  (assert (= "jar" (.getProtocol (io/resource resource))) (str "Non-JAR SDK resource: " resource)))
(assert (.endsWith (-> ansatz.lean.jvm.Lean .getProtectionDomain .getCodeSource .getLocation .getPath)
                   "/ansatz-lean-jvm.jar"))
(let [config (json/read-str (slurp (first *command-line-args*)) :key-fn keyword)]
  (println "NATIVE_LAKE_ACCEPTANCE_BEGIN")
  (flush)
  (let [authored (acceptance/run! (select-keys config [:compiler]))
        _ (println "NATIVE_LAKE_ACCEPTANCE_PASS" (pr-str (:checks authored)))
        external (corpus/run! config)]
    (assert (:passed authored))
    (assert (= #{:cli :fp-sort} (set (map :workload external))))
    (assert (every? #(and (:prepared %) (:artifact-loaded %) (:executed %)) external))
    (spit (:report config)
          (json/write-str {:passed true :authored authored :external external}))
    (println "NATIVE_LAKE_CI_PASS" (:report config))))
(shutdown-agents)
