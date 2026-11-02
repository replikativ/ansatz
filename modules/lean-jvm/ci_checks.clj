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
              "test/entry_checks.clj" "test/extended_entry_checks.clj" "test/scalar_buffer_checks.clj"
              "test-engine/source-contracts/source_authority_contracts.clj"]]
  (load-file file))
(let [basis (ir/linked-basis)
      suites [['ansatz-lean-jvm-build-audit-checks ["."]]
              ['ansatz-lean-jvm-prepare-checks [(:class basis)]]
              ['ansatz-lean-jvm-encoding-checks []]
              ['ansatz-lean-jvm-release-checks ["."]]
              ['ansatz-lean-jvm-facade-checks []]
              ['ansatz-lean-jvm-preparation-api-checks ["."]]
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
