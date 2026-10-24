;; Complete JVM runtime campaign suite. LLVM/Pattern integration remains optional.
;; Supply the authenticated consumer-support source and compact-projection Java
;; classes on the classpath, as for the other restored-runtime campaign checks.
(require '[clojure.java.io :as io])

;; Several native Store fixtures create scoped temporary files under target.
;; A fresh worktree must satisfy that precondition without a prior build.
(let [directory (io/file "target")]
  (.mkdirs directory)
  (when-not (.isDirectory directory)
    (throw (ex-info "Runtime test output path is not a directory" {:path "target"}))))

(require '[clojure.test :as t]
         'prototype.test-runner
         'prototype.bootstrap-function-verification-test
         'prototype.checkpoint-wire-test
         'prototype.compact-kernel-projection-test
         'prototype.compact-import-check-test
         'prototype.source-file-typed-witness-test
         'prototype.source-file-fork-receipt-test
         'prototype.resident-source-test
         'prototype.resident-import-test
         'prototype.globals-overlay-test
         'prototype.restore-consumer-test
         'prototype.program-slot-cache-test
         'prototype.resident-init-prefix-test
         'prototype.resident-init-import-test
         'prototype.source-graph-helper-test
         'prototype.source-graph-runtime-test
         'prototype.source-graph-staged-test
         'prototype.native-init-base-test
         'prototype.project-source-test
         'prototype.classic-header-discovery-test
         'prototype.project-discovery-test
         'prototype.project-loader-test
         'prototype.project-loader-io-test
         'prototype.project-loader-integration-test
         'prototype.project-loader-nonempty-test
         'prototype.typed-extern-test)

(let [result (t/run-all-tests #"^prototype\..*-test$")]
  (shutdown-agents)
  (System/exit (if (zero? (+ (:fail result) (:error result))) 0 1)))
