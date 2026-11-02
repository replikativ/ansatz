(ns engine-contracts
  "Portable canonical engine contracts. Fixtures are independently materialized data."
  (:require [clojure.java.io :as io] [clojure.test :as t]))
(def source-root (.getCanonicalPath (.getParentFile (io/file *file*))))
(load-file (str source-root "/checks/repl.clj"))
(load-file (str source-root "/checks/checks.clj"))
(load-file (str source-root "/checks/continuation-checks.clj"))
(load-file (str source-root "/checks/corpus.clj"))
(load-file (str source-root "/checks/corpus-checks.clj"))
(load-file (str source-root "/checks/extern-checks.clj"))
(load-file (str source-root "/checks/scalar-checks.clj"))
(load-file (str source-root "/checks/main-checks.clj"))
(load-file (str source-root "/checks/fork-checks.clj"))
(load-file (str source-root "/checks/host-checks.clj"))
(load-file (str source-root "/checks/generation-checks.clj"))
(load-file (str source-root "/checks/header-checks.clj"))
(load-file (str source-root "/checks/name-pool-checks.clj"))
(load-file (str source-root "/checks/code-checks.clj"))
(load-file (str source-root "/checks/guest-export-checks.clj"))
(load-file (str source-root "/checks/graph-checks.clj"))
(load-file (str source-root "/checks/module-data-graph.clj"))
(load-file (str source-root "/checks/module-data-graph-checks.clj"))
(load-file (str source-root "/checks/ref-checks.clj"))
(load-file (str source-root "/checks/array-checks.clj"))
(load-file (str source-root "/checks/release-order-checks.clj"))
(load-file (str source-root "/checks/byte-array-checks.clj"))
(load-file (str source-root "/checks/byte-array-empty-checks.clj"))
(load-file (str source-root "/checks/utf8-buffer-checks.clj"))
(load-file (str source-root "/checks/string-checks.clj"))
(load-file (str source-root "/checks/string-completion-checks.clj"))
(load-file (str source-root "/checks/string-pos-checks.clj"))
(load-file (str source-root "/checks/runtime-basics-checks.clj"))
(load-file (str source-root "/checks/task-map-checks.clj"))
(load-file (str source-root "/checks/initialization-checks.clj"))
(load-file (str source-root "/checks/integral-checks.clj"))
(load-file (str source-root "/checks/u64-checks.clj"))
(load-file (str source-root "/checks/u64-narrow-checks.clj"))
(load-file (str source-root "/checks/u64-scalars-checks.clj"))
(load-file (str source-root "/checks/u64-widen-checks.clj"))
(load-file (str source-root "/checks/expression-data-checks.clj"))
(load-file (str source-root "/checks/cached-data-checks.clj"))
(load-file (str source-root "/checks/expr-equality-checks.clj"))
(load-file (str source-root "/checks/level-equality-checks.clj"))
(load-file (str source-root "/checks/f64-checks.clj"))
(load-file (str source-root "/checks/f32-checks.clj"))
(load-file (str source-root "/checks/float-le-checks.clj"))
(load-file (str source-root "/checks/pointer-checks.clj"))
(load-file (str source-root "/checks/logical-sharing-checks.clj"))
(load-file (str source-root "/checks/release-transaction-checks.clj"))
(load-file (str source-root "/checks/sync-task-checks.clj"))
(load-file (str source-root "/checks/stdio-checks.clj"))
(load-file (str source-root "/checks/persistent-checks.clj"))
(load-file (str source-root "/checks/profile-checks.clj"))
(load-file (str source-root "/checks/kernel-projection.clj"))
(load-file (str source-root "/checks/kernel-projection-checks.clj"))
(load-file (str source-root "/checks/host-guest-checks.clj"))
(load-file (str source-root "/checks/kernel-projection-host-guest-checks.clj"))
(load-file (str source-root "/checks/expr-find-checks.clj"))
(load-file (str source-root "/checks/expr-find-ext-checks.clj"))
(load-file (str source-root "/checks/share-common-checks.clj"))
(load-file (str source-root "/checks/level-mvars-checks.clj"))
(load-file (str source-root "/checks/pointer-hash-checks.clj"))
(load-file (str source-root "/checks/pointer-hash-control-checks.clj"))
(load-file (str source-root "/checks/pointer-hash-followup-checks.clj"))
(load-file (str source-root "/checks/expr-transform-policy-checks.clj"))
(load-file (str source-root "/checks/expr-replace-checks.clj"))
(load-file (str source-root "/checks/expr-abstract-checks.clj"))
(load-file (str source-root "/checks/expr-instantiate-checks.clj"))
(load-file (str source-root "/checks/expr-instantiate-control-checks.clj"))
(load-file (str source-root "/checks/expr-full-checks.clj"))
(load-file (str source-root "/checks/expr-full-control-checks.clj"))
(load-file (str source-root "/checks/expr-full-adversarial-checks.clj"))
(load-file (str source-root "/checks/expr-full-native-checks.clj"))
(load-file (str source-root "/checks/expr-full-native-control-checks.clj"))
(load-file (str source-root "/checks/expr-loose-checks.clj"))
(load-file (str source-root "/checks/expr-loose-control-checks.clj"))
(load-file (str source-root "/checks/expr-loose-entry-checks.clj"))
(load-file (str source-root "/checks/expr-quick-order-checks.clj"))
(load-file (str source-root "/checks/expr-quick-order-control-checks.clj"))
(load-file (str source-root "/checks/array-set-checks.clj"))
(load-file (str source-root "/checks/int-checks.clj"))
(load-file (str source-root "/checks/name-equality-checks.clj"))
(load-file (str source-root "/checks/build-identity-checks.clj"))
(load-file (str source-root "/checks/layout-scalar-checks.clj"))
(load-file (str source-root "/checks/u16-checks.clj"))
(load-file (str source-root "/checks/selected-owner-checks.clj"))
(load-file (str source-root "/checks/import-sharing-checks.clj"))
(load-file (str source-root "/checks/void-checks.clj"))
(load-file (str source-root "/checks/catalogue.clj"))
(load-file (str source-root "/checks/catalogue-checks.clj"))
(load-file (str source-root "/checks/source-setup.clj"))
(load-file (str source-root "/checks/composite-source-v4.clj"))
(load-file (str source-root "/checks/source-setup-checks.clj"))

(require 'kernel-contracts.kernel-bridge-test
         'kernel-contracts.kernel-theorem-carrier-test
         'kernel-contracts.compact-kernel-projection-test
         'kernel-contracts.imported-kernel-test
         'kernel-contracts.guarded-kernel-view-test)

(defn run! [artifact]
  (let [basis (java-ir-baseline/class-basis artifact)
        _ (assert (identical? (:loader basis) (.getClassLoader ^Class (:class basis))))
        _ (when (.endsWith ^String artifact ".jar")
            (assert (= "jar" (.getProtocol (.getResource ^Class (:class basis) "Interpreter.class")))))
        groups [
          ["java-ir-baseline-checks" (fn [] (java-ir-baseline-checks/check! basis))]
          ["java-ir-baseline-checks" (fn [] (java-ir-baseline-checks/check! (assoc basis :explicit true)))]
          ["java-ir-continuation-checks" (fn [] (java-ir-continuation-checks/check! basis))]
          ["lean-compatibility-corpus-checks" (fn [] (lean-compatibility-corpus-checks/check! basis))]
          ["java-ir-extern-checks" (fn [] (java-ir-extern-checks/check! basis))]
          ["java-ir-extern-checks" (fn [] (java-ir-extern-checks/check! (assoc basis :explicit true)))]
          ["java-ir-scalar-checks" (fn [] (java-ir-scalar-checks/check! basis))]
          ["java-ir-scalar-checks" (fn [] (java-ir-scalar-checks/check! (assoc basis :explicit true)))]
          ["java-ir-main-checks" (fn [] (java-ir-main-checks/check! basis))]
          ["java-ir-main-checks" (fn [] (java-ir-main-checks/check! (assoc basis :explicit true)))]
          ["java-ir-fork-checks" (fn [] (java-ir-fork-checks/check! basis))]
          ["java-ir-host-checks" (fn [] (java-ir-host-checks/check! basis))]
          ["java-ir-generation-checks" (fn [] (java-ir-generation-checks/check! basis))]
          ["java-ir-header-checks" (fn [] (java-ir-header-checks/check! basis))]
          ["java-ir-code-checks" (fn [] (java-ir-code-checks/check! basis))]
          ["java-ir-guest-export-checks" (fn [] (java-ir-guest-export-checks/check! basis))]
          ["java-ir-guest-export-checks" (fn [] (java-ir-guest-export-checks/check! (assoc basis :explicit true)))]
          ["java-ir-graph-checks" (fn [] (java-ir-graph-checks/check! basis))]
          ["java-ir-module-data-graph-checks" (fn [] (clojure.test/run-tests 'java-ir-module-data-graph-checks))]
          ["java-ir-ref-checks" (fn [] (java-ir-ref-checks/check! basis))]
          ["java-ir-ref-checks" (fn [] (java-ir-ref-checks/check! (assoc basis :explicit true)))]
          ["java-ir-array-checks" (fn [] (java-ir-array-checks/check! basis))]
          ["java-ir-array-checks" (fn [] (java-ir-array-checks/check! (assoc basis :explicit true)))]
          ["java-ir-release-order-checks" (fn [] (java-ir-release-order-checks/check! basis))]
          ["java-ir-release-order-checks" (fn [] (java-ir-release-order-checks/check! (assoc basis :explicit true)))]
          ["java-ir-byte-array-checks" (fn [] (java-ir-byte-array-checks/check! basis))]
          ["java-ir-byte-array-checks" (fn [] (java-ir-byte-array-checks/check! (assoc basis :explicit true)))]
          ["java-ir-byte-array-empty-checks" (fn [] (java-ir-byte-array-empty-checks/check! basis))]
          ["java-ir-utf8-buffer-checks" (fn [] (java-ir-utf8-buffer-checks/check! basis))]
          ["java-ir-string-checks" (fn [] (java-ir-string-checks/check! basis))]
          ["java-ir-string-checks" (fn [] (java-ir-string-checks/check! (assoc basis :explicit true)))]
          ["java-ir-string-completion-checks" (fn [] (java-ir-string-completion-checks/check! basis))]
          ["java-ir-string-completion-checks" (fn [] (java-ir-string-completion-checks/check! (assoc basis :explicit true)))]
          ["java-ir-string-pos-checks" (fn [] (java-ir-string-pos-checks/check! basis))]
          ["java-ir-string-pos-checks" (fn [] (java-ir-string-pos-checks/check! (assoc basis :explicit true)))]
          ["java-ir-runtime-basics-checks" (fn [] (java-ir-runtime-basics-checks/check! basis))]
          ["java-ir-runtime-basics-checks" (fn [] (java-ir-runtime-basics-checks/check! (assoc basis :explicit true)))]
          ["java-ir-task-map-checks" (fn [] (java-ir-task-map-checks/check! basis))]
          ["java-ir-task-map-checks" (fn [] (java-ir-task-map-checks/check! (assoc basis :explicit true)))]
          ["java-ir-initialization-checks" (fn [] (java-ir-initialization-checks/check! basis))]
          ["java-ir-initialization-checks" (fn [] (java-ir-initialization-checks/check! (assoc basis :explicit true)))]
          ["java-ir-integral-checks" (fn [] (java-ir-integral-checks/check! basis))]
          ["java-ir-integral-checks" (fn [] (java-ir-integral-checks/check! (assoc basis :explicit true)))]
          ["java-ir-u64-checks" (fn [] (java-ir-u64-checks/check! basis))]
          ["java-ir-u64-checks" (fn [] (java-ir-u64-checks/check! (assoc basis :explicit true)))]
          ["java-ir-u64-narrow-checks" (fn [] (java-ir-u64-narrow-checks/check! basis))]
          ["java-ir-u64-narrow-checks" (fn [] (java-ir-u64-narrow-checks/check! (assoc basis :explicit true)))]
          ["java-ir-u64-scalars-checks" (fn [] (java-ir-u64-scalars-checks/check! basis))]
          ["java-ir-u64-scalars-checks" (fn [] (java-ir-u64-scalars-checks/check! (assoc basis :explicit true)))]
          ["java-ir-u64-widen-checks" (fn [] (java-ir-u64-widen-checks/check! basis))]
          ["java-ir-u64-widen-checks" (fn [] (java-ir-u64-widen-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expression-data-checks" (fn [] (java-ir-expression-data-checks/check! basis))]
          ["java-ir-expression-data-checks" (fn [] (java-ir-expression-data-checks/check! (assoc basis :explicit true)))]
          ["java-ir-cached-data-checks" (fn [] (java-ir-cached-data-checks/check! basis))]
          ["java-ir-cached-data-checks" (fn [] (java-ir-cached-data-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-equality-checks" (fn [] (java-ir-expr-equality-checks/check! basis))]
          ["java-ir-expr-equality-checks" (fn [] (java-ir-expr-equality-checks/check! (assoc basis :explicit true)))]
          ["java-ir-level-equality-checks" (fn [] (java-ir-level-equality-checks/check! basis))]
          ["java-ir-level-equality-checks" (fn [] (java-ir-level-equality-checks/check! (assoc basis :explicit true)))]
          ["java-ir-f64-checks" (fn [] (java-ir-f64-checks/check! basis))]
          ["java-ir-float-le-checks" (fn [] (java-ir-float-le-checks/check! basis))]
          ["java-ir-float-le-checks" (fn [] (java-ir-float-le-checks/check! (assoc basis :explicit true)))]
          ["java-ir-f64-checks" (fn [] (java-ir-f64-checks/check! (assoc basis :explicit true)))]
          ["java-ir-pointer-checks" (fn [] (java-ir-pointer-checks/check! basis))]
          ["java-ir-pointer-checks" (fn [] (java-ir-pointer-checks/check! (assoc basis :explicit true)))]
          ["java-ir-pointer-hash-checks" (fn [] (java-ir-pointer-hash-checks/check! basis))]
          ["java-ir-pointer-hash-checks" (fn [] (java-ir-pointer-hash-checks/check! (assoc basis :explicit true)))]
          ["java-ir-pointer-hash-control-checks" (fn [] (java-ir-pointer-hash-control-checks/check! basis))]
          ["java-ir-pointer-hash-control-checks" (fn [] (java-ir-pointer-hash-control-checks/check! (assoc basis :explicit true)))]
          ["java-ir-pointer-hash-followup-checks" (fn [] (java-ir-pointer-hash-followup-checks/check! basis))]
          ["java-ir-pointer-hash-followup-checks" (fn [] (java-ir-pointer-hash-followup-checks/check! (assoc basis :explicit true)))]
          ["java-ir-logical-sharing-checks" (fn [] (java-ir-logical-sharing-checks/check! basis))]
          ["java-ir-logical-sharing-checks" (fn [] (java-ir-logical-sharing-checks/check! (assoc basis :explicit true)))]
          ["java-ir-release-transaction-checks" (fn [] (java-ir-release-transaction-checks/check! (assoc basis :explicit true)))]
          ["java-ir-sync-task-checks" (fn [] (java-ir-sync-task-checks/check! (assoc basis :explicit true)))]
          ["java-ir-stdio-checks" (fn [] (java-ir-stdio-checks/check! basis))]
          ["java-ir-persistent-checks" (fn [] (java-ir-persistent-checks/check! basis))]
          ["java-ir-persistent-checks" (fn [] (java-ir-persistent-checks/check! (assoc basis :explicit true)))]
          ["java-ir-profile-checks" (fn [] (java-ir-profile-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-find-checks" (fn [] (java-ir-expr-find-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-find-ext-checks" (fn [] (java-ir-expr-find-ext-checks/check! (assoc basis :explicit true)))]
          ["java-ir-share-common-checks" (fn [] (java-ir-share-common-checks/check! (assoc basis :explicit true)))]
          ["java-ir-level-mvars-checks" (fn [] (java-ir-level-mvars-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-transform-policy-checks" (fn [] (java-ir-expr-transform-policy-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-replace-checks" (fn [] (java-ir-expr-replace-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-abstract-checks" (fn [] (java-ir-expr-abstract-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-instantiate-checks" (fn [] (java-ir-expr-instantiate-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-instantiate-control-checks" (fn [] (java-ir-expr-instantiate-control-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-full-checks" (fn [] (java-ir-expr-full-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-full-control-checks" (fn [] (java-ir-expr-full-control-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-full-adversarial-checks" (fn [] (java-ir-expr-full-adversarial-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-full-native-checks" (fn [] (java-ir-expr-full-native-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-full-native-control-checks" (fn [] (java-ir-expr-full-native-control-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-loose-checks" (fn [] (java-ir-expr-loose-checks/check! basis))]
          ["java-ir-expr-loose-checks" (fn [] (java-ir-expr-loose-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-loose-control-checks" (fn [] (java-ir-expr-loose-control-checks/check! basis))]
          ["java-ir-expr-loose-control-checks" (fn [] (java-ir-expr-loose-control-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-loose-entry-checks" (fn [] (java-ir-expr-loose-entry-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-quick-order-checks" (fn [] (java-ir-expr-quick-order-checks/check! basis))]
          ["java-ir-expr-quick-order-checks" (fn [] (java-ir-expr-quick-order-checks/check! (assoc basis :explicit true)))]
          ["java-ir-expr-quick-order-control-checks" (fn [] (java-ir-expr-quick-order-control-checks/check! basis))]
          ["java-ir-expr-quick-order-control-checks" (fn [] (java-ir-expr-quick-order-control-checks/check! (assoc basis :explicit true)))]
          ["java-ir-array-set-checks" (fn [] (java-ir-array-set-checks/check! basis))]
          ["java-ir-array-set-checks" (fn [] (java-ir-array-set-checks/check! (assoc basis :explicit true)))]
          ["java-ir-kernel-projection-checks" (fn [] (java-ir-kernel-projection-checks/check! basis))]
          ["java-ir-host-guest-checks" (fn [] (java-ir-host-guest-checks/check! basis))]
          ["java-ir-kernel-projection-host-guest-checks" (fn [] (java-ir-kernel-projection-host-guest-checks/check! basis))]
          ["java-ir-int-checks" (fn [] (java-ir-int-checks/check! basis))]
          ["java-ir-int-checks" (fn [] (java-ir-int-checks/check! (assoc basis :explicit true)))]
          ["java-ir-name-equality-checks" (fn [] (java-ir-name-equality-checks/check! basis))]
          ["java-ir-name-equality-checks" (fn [] (java-ir-name-equality-checks/check! (assoc basis :explicit true)))]
          ["java-ir-build-identity-checks" (fn [] (java-ir-build-identity-checks/check! basis))]
          ["java-ir-build-identity-checks" (fn [] (java-ir-build-identity-checks/check! (assoc basis :explicit true)))]
          ["java-ir-selected-owner-checks" (fn [] (java-ir-selected-owner-checks/check! basis))]
          ["java-ir-selected-owner-checks" (fn [] (java-ir-selected-owner-checks/check! (assoc basis :explicit true)))]
          ["java-ir-import-sharing-checks" (fn [] (java-ir-import-sharing-checks/check! basis))]
          ["java-ir-import-sharing-checks" (fn [] (java-ir-import-sharing-checks/check! (assoc basis :explicit true)))]
          ["java-ir-void-checks" (fn [] (java-ir-void-checks/check! basis))]
          ["java-ir-void-checks" (fn [] (java-ir-void-checks/check! (assoc basis :explicit true)))]
          ["java-ir-catalogue-checks" (fn [] (java-ir-catalogue-checks/check!))]
          ["java-ir-source-setup-checks" (fn [] (java-ir-source-setup-checks/check!))]
          ["java-ir-layout-scalar-checks" (fn [] (java-ir-layout-scalar-checks/check! basis))]
          ["java-ir-layout-scalar-checks" (fn [] (java-ir-layout-scalar-checks/check! (assoc basis :explicit true)))]
          ["java-ir-u16-checks" (fn [] (java-ir-u16-checks/check! basis))]
          ["java-ir-u16-checks" (fn [] (java-ir-u16-checks/check! (assoc basis :explicit true)))]
          ["java-ir-name-pool-checks" (fn [] (java-ir-name-pool-checks/check! basis))]
          ["java-ir-f32-checks" (fn [] (java-ir-f32-checks/check! basis))]
          ["java-ir-f32-checks" (fn [] (java-ir-f32-checks/check! (assoc basis :explicit true)))]
          ["kernel-contracts.kernel-bridge-test" (fn [] (t/run-tests 'kernel-contracts.kernel-bridge-test))]
          ["kernel-contracts.kernel-theorem-carrier-test" (fn [] (t/run-tests 'kernel-contracts.kernel-theorem-carrier-test))]
          ["kernel-contracts.compact-kernel-projection-test" (fn [] (t/run-tests 'kernel-contracts.compact-kernel-projection-test))]
          ["kernel-contracts.imported-kernel-test" (fn [] (t/run-tests 'kernel-contracts.imported-kernel-test))]
          ["kernel-contracts.guarded-kernel-view-test" (fn [] (t/run-tests 'kernel-contracts.guarded-kernel-view-test))]
        ]
        results (mapv (fn [[label check!]]
                        (let [expected (set (for [[_ v] (ns-interns (symbol label))
                                                  :when (:test (meta v))] v))
                              seen (atom #{}) report t/report
                              result (with-redefs [t/report (fn [event]
                                                            (when (= :begin-test-var (:type event))
                                                              (swap! seen conj (:var event)))
                                                            (report event))]
                                       (check!))]
                          (assert (and (seq expected) (= expected @seen)
                                       (= (count expected) (:test result)))
                                  (str "Missing contract tests: " label))
                          (assoc result :group label))) groups)]
    {:basis basis :results results
     :passed? (every? #(zero? (+ (:fail %) (:error %))) results)}))

(when (seq *command-line-args*)
  (let [result (run! (first *command-line-args*))]
    (println "ENGINE_CONTRACTS" {:groups (count (:results result))
                                 :tests (reduce + (map :test (:results result)))
                                 :assertions (reduce + (map #(+ (:pass %) (:fail %) (:error %)) (:results result)))
                                 :passed (:passed? result)})
    (shutdown-agents)
    (System/exit (if (:passed? result) 0 1))))
