(ns ansatz-lean-jvm-release-checks
  "Release-byte custody models. Run in the retained producer JVM, no guest/native work."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io]
            [ansatz-lean-jvm-release :as release])
  (:import [java.nio.file Files]
           [java.util.zip ZipOutputStream ZipEntry]))
(def ^:dynamic *module-root* nil)
(defn rejected? [f] (try (f) false (catch clojure.lang.ExceptionInfo _ true)))
(defn write-jar! [path pom metadata]
  (with-open [output (ZipOutputStream. (io/output-stream path))]
    (doseq [[name content] [[release/pom-entry pom] [release/metadata-entry (pr-str metadata)]]]
      (.putNextEntry output (ZipEntry. name))
      (.write output (.getBytes content java.nio.charset.StandardCharsets/UTF_8))
      (.closeEntry output))))
(deftest exact-reviewed-bytes-and-version-required
  (let [parent (io/file *module-root* "target/release-checks")
        _ (.mkdirs parent)
        root (.toFile (Files/createTempDirectory (.toPath parent) "release-"
                         (make-array java.nio.file.attribute.FileAttribute 0)))
        jar (str (io/file root "sdk.jar")) pom (str (io/file root "pom.xml"))
        receipt (str (io/file root "release.edn"))
        xml "<project><groupId>org.replikativ</groupId><artifactId>ansatz-lean-jvm</artifactId><version>0.2.1234</version></project>"
        metadata {:schema "ansatz-lean-jvm-runtime/1" :java-release 17
                  :engine-closure-sha256 (apply str (repeat 64 "b"))
                  :artifact-version "0.2.1234" :engine-source-sha256 (apply str (repeat 64 "a"))
                  :public-project-api false :native-compiler-included false}]
    (try
      (spit pom xml)
      (write-jar! jar xml metadata)
      (let [prepared (release/prepare! {:jar-file jar :pom-file pom :version "0.2.1234" :output receipt})]
        (is (false? (:public-project-api prepared)))
        (is (= jar (:jar-file (release/verify! {:receipt receipt :version "0.2.1234"})))))
      (is (rejected? #(release/verify! {:receipt receipt :version "0.2.1235"})))
      (is (rejected? #(release/verify! {:receipt receipt})))
      (spit pom (str xml "\n"))
      (is (rejected? #(release/verify! {:receipt receipt :version "0.2.1234"})))
      (spit pom xml)
      (write-jar! jar xml (assoc metadata :artifact-version "0.2.1235"))
      (is (rejected? #(release/prepare! {:jar-file jar :pom-file pom :version "0.2.1234" :output receipt})))
      (write-jar! jar xml metadata)
      (spit jar "changed archive")
      (is (try (release/verify! {:receipt receipt :version "0.2.1234"}) false
               (catch java.util.zip.ZipException _ true)))
      (finally (doseq [file (reverse (file-seq root))] (io/delete-file file))))))
(deftest root-version-format-is-explicit
  (is (= "0.2.1234" (release/check-version! "0.2.1234")))
  (doseq [version [nil "0.1.0-experimental" "0.2.1-SNAPSHOT" "../../artifact"]]
    (is (rejected? #(release/check-version! version)))))
(defn check! [module-root]
  (binding [*module-root* module-root] (run-tests 'ansatz-lean-jvm-release-checks)))
