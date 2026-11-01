(require '[clojure.java.io :as io]
         '[ansatz.lean.jvm.ir :as ir]
         '[ansatz.lean.jvm.project]
         '[ansatz-lean-jvm-signature-checks :as signature-models]
         '[ansatz-lean-jvm-codec-checks :as codec-models]
         '[ansatz-lean-jvm-value-checks :as value-models]
         '[ansatz-lean-jvm-argument-checks :as argument-models]
         '[ansatz-lean-jvm-module-startup-models :as module-models]
         '[ansatz-lean-jvm-publisher-models :as publisher-models]
         '[ansatz-lean-jvm-capability-models :as capability-models]
         '[ansatz-lean-jvm-lifecycle-models :as lifecycle-models]
         '[ansatz-lean-jvm-artifact-models :as artifact-models])

;; Runtime resources and classes must come from the built SDK, never src/ or
;; target/classes. Producer audit helpers/models remain separate test inputs.
(doseq [resource ["ansatz/lean/jvm/ir.clj" "ansatz/lean/jvm/project.clj"
                  "ansatz/lean/jvm/startup.clj" "ansatz/lean/jvm/artifact.clj"]]
  (assert (= "jar" (.getProtocol (io/resource resource))) (str "Non-JAR SDK resource: " resource)))
(let [source (-> (Class/forName "ansatz.lean.jvm.Lean") .getProtectionDomain .getCodeSource .getLocation .getPath)]
  (assert (.endsWith source "/ansatz-lean-jvm.jar") "Java facade must come from the built SDK JAR"))

(load-file "ansatz_lean_jvm_build_audit.clj")
(load-file "ansatz_lean_jvm_release.clj")
(doseq [file ["test/build_audit_checks.clj" "test/prepare_checks.clj"
              "test/encoding_checks.clj" "test/release_checks.clj" "test/facade_checks.clj"
              "test/entry_checks.clj" "test/extended_entry_checks.clj"]]
  (load-file file))
(let [basis (ir/linked-basis)
      results [(ansatz-lean-jvm-build-audit-checks/check! ".")
               (ansatz-lean-jvm-prepare-checks/check! (:class basis))
               (ansatz-lean-jvm-encoding-checks/check!)
               (ansatz-lean-jvm-release-checks/check! ".")
               (ansatz-lean-jvm-facade-checks/check!)
               (module-models/check!) (publisher-models/check!)
               (capability-models/check! basis) (lifecycle-models/check! basis)
               (artifact-models/check!)
               (signature-models/check!) (codec-models/check!)
               (ansatz-lean-jvm-entry-checks/check! ".")
               (ansatz-lean-jvm-extended-entry-checks/check! ".")
               (value-models/check! "test/fixtures/value-codec-witnesses.json")
               (argument-models/check! "test/fixtures/value-codec-witnesses.json")]
      tests (reduce + (map :test results))
      assertions (reduce + (map #(+ (:pass %) (:fail %) (:error %)) results))
      successful (and (= 103 tests) (= 536 assertions)
                      (every? #(zero? (+ (:fail %) (:error %))) results))]
  (println "SDK_JAR_MODELS" {:tests tests :assertions assertions :successful successful})
  (shutdown-agents)
  (System/exit (if successful 0 1)))
