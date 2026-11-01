;; Coherent protocol models, bounded 17-CI admission fixtures and small runtimes.
;; No full Init image, genuine frontend/provider run or bootstrap restore.
;; Run from experiments/lean-ir with src, test,
;; main-library sources, coherent Java classes and dependencies on the classpath.
(require '[clojure.test :as t] '[clojure.java.io :as io])
(when-let [expected (System/getProperty "ansatz.coherent.test.class-root")]
  (doseq [name ["ansatz.kernel.Env" "ansatz.kernel.TypeChecker" "ansatz.runtime.HeapOverlay" "prototype.TypedLongMemo"]]
    (assert (= (str (.toURL (.toURI (io/file expected))))
               (str (-> (Class/forName name) .getProtectionDomain .getCodeSource .getLocation))))))
(def observed (atom #{}))
(defmethod t/report :begin-test-var [event] (swap! observed conj (:var event)))
(defmethod t/report :fail [event]
  (t/inc-report-counter :fail)
  (println "ASSERTION_FAILURE" (:file event) (:line event)))
(defmethod t/report :error [event]
  (t/inc-report-counter :error)
  (println "TEST_ERROR" (:file event) (:line event))
  (loop [cause (:actual event) remaining 8]
    (when (and cause (pos? remaining))
      (println (.getName (class cause)))
      (doseq [frame (take 5 (.getStackTrace ^Throwable cause))] (println (str frame)))
      (recur (.getCause ^Throwable cause) (dec remaining)))))
(try
  ;; Loading definitions must never call construct!, run!, restore or a guest.
  (doseq [n '[prototype.coherent-source-preparation prototype.coherent-helper-value
              prototype.coherent-typed-eio prototype.coherent-execution
              prototype.coherent-stage-guards prototype.coherent-campaign
              prototype.coherent-stage-guards-test prototype.coherent-owner-ledger-test prototype.coherent-consumer-profile-test
              prototype.coherent-boundary-test prototype.coherent-jvm-lifecycle-test
              prototype.resident-code-validation-test prototype.executable-closure-proof-test prototype.continuation-layout-test
              prototype.resident-branch-retirement-test prototype.coherent-prefix-retirement-test]]
    (require n))
  (assert (nil? ((ns-resolve 'prototype.coherent-campaign 'checkpoint))))
  (let [vars (set (filter #(-> % meta :test) (mapcat #(vals (ns-publics %)) '[prototype.coherent-stage-guards-test prototype.coherent-owner-ledger-test prototype.coherent-consumer-profile-test prototype.coherent-boundary-test prototype.coherent-jvm-lifecycle-test prototype.resident-code-validation-test prototype.executable-closure-proof-test prototype.continuation-layout-test prototype.resident-branch-retirement-test prototype.coherent-prefix-retirement-test])))
        _ (assert (= 75 (count vars)))
        counters (binding [t/*report-counters* (ref t/*initial-report-counters*)]
                   (t/test-vars (sort-by #(str (:name (meta %))) vars))
                   @t/*report-counters*)]
    (assert (= vars @observed))
    (assert (zero? (+ (:fail counters) (:error counters))))
    (assert (= 75 (:test counters)))
    (assert (nil? ((ns-resolve 'prototype.coherent-campaign 'checkpoint))))
    (println (assoc counters :scope "definitions-contract-and-protocol-models-only"))
    (println "COHERENT_INFRASTRUCTURE_75_PASS")
    ;; Separate bounded fixture scope: actual tiny Store/getter/helper execution,
    ;; privately modelled Factory/escrow facts and captured frontend IR. These are
    ;; not full Init admission, native finalization or genuine provider evidence.
    ;; Tiny synthetic Init transports use temporary files under this directory.
    (.mkdirs (io/file "target"))
    (let [nss '[prototype.full-init-admission-test
                prototype.coherent-source-preparation-test prototype.coherent-helper-value-test
                prototype.resident-admitted-init-prefix-test prototype.coherent-jvm-slice-test]
          _ (doseq [n nss] (require n))
          fixture-vars (set (filter #(-> % meta :test)
                                   (mapcat #(vals (ns-publics %)) nss)))
          _ (assert (= 31 (count fixture-vars)))
          _ (reset! observed #{})
          counters (binding [t/*report-counters* (ref t/*initial-report-counters*)]
                     (t/test-vars (sort-by #(str (:name (meta %))) fixture-vars))
                     @t/*report-counters*)]
      (assert (= fixture-vars @observed))
      (assert (= 31 (:test counters)))
      (assert (zero? (+ (:fail counters) (:error counters))))
      (assert (nil? ((ns-resolve 'prototype.coherent-campaign 'checkpoint))))
      (assert (nil? ((ns-resolve 'prototype.coherent-source-preparation 'checkpoint))))
      (assert (nil? ((ns-resolve 'prototype.coherent-source-preparation 'checking-checkpoint))))
      (assert (nil? ((ns-resolve 'prototype.coherent-helper-value 'checkpoint))))
      (assert (nil? (:controller ((ns-resolve 'prototype.coherent-jvm-slice 'checkpoint)))))
      (println (assoc counters :scope "bounded-artifact-admission-and-resident-provider-models"))
      (println "ARTIFACT_ADMISSION_PROVIDER_MODELS_31_PASS"))
    ;; Distinct scope: these explicit small programs execute guest instructions,
    ;; but never load Init, a Source, bootstrap or the genuine frontend.
    (require 'prototype.unchanged-host-resume-test)
    (require 'prototype.scalar-test)
    (reset! observed #{})
    (let [runtime-vars (conj (set (filter #(-> % meta :test)
                                        (vals (ns-publics 'prototype.unchanged-host-resume-test))))
                             (ns-resolve 'prototype.scalar-test
                                         'scalar-storage-rejects-uninitialized-out-of-bounds-and-shared-writes))
          _ (assert (= 15 (count runtime-vars)))
          runtime-counters (binding [t/*report-counters* (ref t/*initial-report-counters*)]
                             (t/test-vars (sort-by #(str (:name (meta %))) runtime-vars))
                             @t/*report-counters*)]
      (assert (= runtime-vars @observed))
      (assert (= 15 (:test runtime-counters)))
      (assert (zero? (+ (:fail runtime-counters) (:error runtime-counters))))
      (assert (nil? ((ns-resolve 'prototype.coherent-campaign 'checkpoint))))
      (println (assoc runtime-counters :scope "small-explicit-host-storage-runtime-programs"))
      (println "HOST_STORAGE_RUNTIME_15_PASS"))
    ;; Bounded branching evidence: checked-in generated IR/model observations;
    ;; no native Lean executable, Init image or external host IO is required.
    (let [nss '[prototype.branch-lab-test prototype.host-cells-lab-test
                prototype.klara-branch-generated-test prototype.klara-branch-bridge-test
                prototype.klara-branch-model-test]
          _ (doseq [n nss] (require n))
          branch-vars (set (filter #(-> % meta :test)
                                  (mapcat #(vals (ns-publics %)) nss)))
          _ (assert (= 25 (count branch-vars)))
          _ (reset! observed #{})
          counters (binding [t/*report-counters* (ref t/*initial-report-counters*)]
                     (t/test-vars (sort-by #(str (:name (meta %))) branch-vars))
                     @t/*report-counters*)]
      (assert (= branch-vars @observed))
      (assert (= 25 (:test counters)))
      (assert (zero? (+ (:fail counters) (:error counters))))
      (assert (nil? ((ns-resolve 'prototype.coherent-campaign 'checkpoint))))
      (println (assoc counters :scope "bounded-klara-lean-branch-runtime-and-model-fixtures"))
      (println "KLARA_LEAN_BRANCH_25_PASS"))
    (shutdown-agents)
    (System/exit 0))
  (catch Throwable failure
    (println "COHERENT_INFRASTRUCTURE_FAILURE" (.getName (class failure)))
    (loop [cause failure remaining 8]
      (when (and cause (pos? remaining))
        (println (.getName (class cause)))
        (doseq [frame (take 5 (.getStackTrace ^Throwable cause))] (println (str frame)))
        (recur (.getCause ^Throwable cause) (dec remaining))))
    (shutdown-agents)
    (System/exit 2)))
