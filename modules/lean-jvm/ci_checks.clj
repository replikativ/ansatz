(require '[clojure.test :as t]
         '[clojure.java.io :as io]
         '[ansatz.lean.jvm.ir :as ir]
         '[ansatz.lean.jvm.project]
         '[ansatz-lean-jvm-signature-checks]
         '[ansatz-lean-jvm-codec-checks]
         '[ansatz-lean-jvm-value-checks]
         '[ansatz-lean-jvm-value-convention-checks]
         '[ansatz-lean-jvm-argument-checks]
         '[ansatz-lean-jvm-producer-checks]
         '[ansatz-lean-jvm-boundary-checks]
         '[ansatz-lean-jvm-module-startup-models]
         '[ansatz-lean-jvm-publisher-models]
         '[ansatz-lean-jvm-capability-models]
         '[ansatz-lean-jvm-lifecycle-models]
         '[ansatz-lean-jvm-artifact-models])

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
              "test/preparation_api_checks.clj"
              "test/installed_import_checks.clj"
              "test/string_action_checks.clj"
              "test/filesystem_profile_checks.clj"
              "test/filesystem_layout_checks.clj"
              "test/filesystem_lifecycle_checks.clj"
              "test/filesystem_writing_checks.clj"
              "test/entry_checks.clj" "test/extended_entry_checks.clj" "test/scalar_buffer_checks.clj"
              "test/type_graph_checks.clj"
              "test/used_products_checks.clj"
              "test/representation_checks.clj"
              "test/compiler_products_checks.clj"
              "test/compiler_bundle_checks.clj"
              "test/entry_v3_checks.clj"
              "test/representation_witness_checks.clj"
              "test/representation_entry_checks.clj"
              "test/compiler_v3_reconciliation_checks.clj"
              "test/nominal_artifact_checks.clj"
              "test/native_transport_checks.clj"
              "test/io_error_checks.clj"
              "test-engine/source-contracts/source_authority_contracts.clj"]]
  (load-file file))
(let [basis (ir/linked-basis)
      suites [['ansatz-lean-jvm-build-audit-checks ["."]]
              ['ansatz-lean-jvm-prepare-checks [(:class basis)]]
              ['ansatz-lean-jvm-encoding-checks []]
              ['ansatz-lean-jvm-release-checks ["."]]
              ['ansatz-lean-jvm-facade-checks []]
              ['ansatz-lean-jvm-preparation-api-checks ["."]]
              ['installed-import-checks []]
              ['ansatz-lean-jvm-string-action-checks []]
              ['ansatz-lean-jvm-filesystem-profile-checks []]
              ['ansatz-lean-jvm-filesystem-layout-checks []]
              ['ansatz-lean-jvm-filesystem-lifecycle-checks ["."]]
              ['ansatz-lean-jvm-filesystem-writing-checks ["."]]
              ['ansatz-lean-jvm-module-startup-models []]
              ['ansatz-lean-jvm-publisher-models []]
              ['ansatz-lean-jvm-capability-models [basis]]
              ['ansatz-lean-jvm-lifecycle-models [basis]]
              ['ansatz-lean-jvm-artifact-models []]
              ['ansatz-lean-jvm-signature-checks []]
              ['ansatz-lean-jvm-codec-checks []]
              ['ansatz-lean-jvm-entry-checks ["."]]
              ['ansatz-lean-jvm-extended-entry-checks ["."]]
              ['ansatz-lean-jvm-value-checks ["test/fixtures/value-codec-witnesses.json"]]
              ['ansatz-lean-jvm-value-convention-checks []]
              ['ansatz-lean-jvm-argument-checks ["test/fixtures/value-codec-witnesses.json"]]
              ['ansatz-lean-jvm-producer-checks ["."]]
              ['ansatz-lean-jvm-boundary-checks ["."]]
              ['ansatz-lean-jvm-scalar-buffer-checks []]
              ['ansatz-lean-jvm-type-graph-checks []]
              ['ansatz-lean-jvm-used-products-checks []]
              ['ansatz-lean-jvm-representation-checks ["test/fixtures/nominal-observations/observations.json"]]
              ['ansatz-lean-jvm-compiler-products-checks []]
              ['ansatz-lean-jvm-compiler-bundle-checks ["."]]
              ['ansatz-lean-jvm-entry-v3-checks ["test/fixtures/nominal-entry-v3/entry-evidence.json"
                                               "test/fixtures/nominal-entry-v3/oracle-entry-evidence.json"]]
              ['ansatz-lean-jvm-representation-witness-checks ["test/fixtures/nominal-entry-v3/builtin-observations.json"]]
              ['ansatz-lean-jvm-representation-entry-checks ["test/fixtures/nominal-entry-v3/entry-evidence.json"]]
              ['ansatz-lean-jvm-compiler-v3-reconciliation-checks ["test/fixtures/nominal-entry-v3/oracle-entry-evidence.json"
                                                                 "test/fixtures/nominal-entry-v3/typed-export.jsonl"]]
              ['ansatz-lean-jvm-nominal-artifact-checks ["test/fixtures/nominal-entry-v3/oracle-entry-evidence.json"
                                                      "test/fixtures/nominal-entry-v3/producer-build-receipt.json"]]
              ['ansatz-lean-jvm-native-transport-checks []]
              ['ansatz-lean-jvm-io-error-checks []]
              ['source-authority-contracts ["."]]]
      results (mapv
               (fn [[namespace arguments]]
                 (let [expected (set (for [[_ v] (ns-publics namespace)
                                           :when (:test (meta v))] v))
                       seen (atom #{})
                       report t/report
                       result (with-redefs [t/report (fn [event]
                                                      (when (= :begin-test-var (:type event))
                                                        (swap! seen conj (:var event)))
                                                      (report event))]
                                (apply (ns-resolve namespace 'check!) arguments))]
                   (assoc result :complete (and (seq expected) (= expected @seen)
                                               (= (count expected) (:test result))))))
               suites)
      tests (reduce + (map :test results))
      assertions (reduce + (map #(+ (:pass %) (:fail %) (:error %)) results))
      successful (every? #(and (:complete %) (zero? (+ (:fail %) (:error %)))) results)]
  (println "SDK_JAR_MODELS" {:tests tests :assertions assertions :successful successful})
  (shutdown-agents)
  (System/exit (if successful 0 1)))
