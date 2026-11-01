;; Run from experiments/lean-ir. Metadata and filesystem contracts only:
;; no Lean process, guest execution, Init replay or store loading.
(ns native-project-contracts
  (:require [clojure.java.io :as io]
            [clojure.test :refer [deftest run-tests]])
  (:import [java.nio.file Files]
           [java.nio.file.attribute FileAttribute]
           [java.util Comparator]))

(def source-root (.getParentFile (.getParentFile (.getCanonicalFile (io/file *file*)))))
(defn source! [relative] (load-file (str (io/file source-root relative))))
(source! "research/unchanged-program-benchmark.clj")
(source! "research/java-ir-baseline/repl.clj")
(doseq [file ["runner" "compiler" "compiler-models" "local-project"
              "local-project-models" "project-evidence" "project-evidence-models"]]
  (source! (str "research/java-ir-baseline/native-project/" file ".clj")))

(def workspace
  (let [parent (.toPath (io/file "target/native-project-contracts"))]
    (Files/createDirectories parent (make-array FileAttribute 0))
    (Files/createTempDirectory parent "models-" (make-array FileAttribute 0))))

(deftest capture-and-cache-filesystem-contracts
  (native-local-project-models-v2/check-files! workspace)
  (native-local-project-models-v2/check-cache-files! workspace))

(let [results (try
                [(native-project-compiler-models-v1/check! workspace)
                 (native-local-project-models-v2/check!)
                 (native-project-build-evidence-models-v2/check!)
                 (run-tests 'native-project-contracts)]
                (finally
                  ;; Files.walk does not follow links created by the models.
                  (with-open [paths (Files/walk workspace (make-array java.nio.file.FileVisitOption 0))]
                    (doseq [path (iterator-seq (.iterator (.sorted paths (Comparator/reverseOrder))))]
                      (Files/deleteIfExists path)))))]
  (shutdown-agents)
  (System/exit
   (if (and (= [15 6 7 1] (mapv :test results))
            (every? #(zero? (+ (:fail %) (:error %))) results)) 0 1)))
