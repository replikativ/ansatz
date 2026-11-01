(ns ansatz-lean-jvm-build-audit-checks
  "Source-only inventory/dependency gate; never loads the interpreter."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.edn :as edn] [clojure.java.io :as io]
            [ansatz-lean-jvm-build-audit :as audit])
  (:import [java.nio.file Files]))
(def ^:dynamic *module-root* nil)
(defn rejected? [f] (try (f) false (catch clojure.lang.ExceptionInfo _ true)))
(defn closure [] (edn/read-string (slurp (io/file *module-root* "runtime-closure.edn"))))
(deftest actual-package-is-explicit-and-source-only
  (let [result (audit/verify! {:module-root *module-root*})]
    (is (= 17 (:sources result))) (is (= 3 (:resources result)))
    (is (= 11 (:java-sources result)))
    (is (= '{org.clojure/clojure {:mvn/version "1.12.0"}
             org.clojure/data.json {:mvn/version "2.5.1"}} (:runtime-dependencies result)))))
(deftest source-paths-and-dependency-closure-cannot-drift
  (let [original (closure)]
    (doseq [changed [(assoc-in original [:sources 0 :path] "prototype/machine.cljc")
                     (assoc-in original [:sources 0 :namespace] 'native-project-entry-v1)
                     (update original :sources conj (first (:sources original)))
                     (assoc-in original [:java :path] "src-java/Interpreter.java")
                     (assoc original :resources ["research/repl.clj"])
                     (assoc-in original [:runtime-dependencies 'org.replikativ/pattern] {:mvn/version "1.0.452"})]]
      (is (rejected? #(audit/validate-manifest! changed))))))
(deftest runtime-ns-admission-checks-actual-requires
  (is (audit/check-namespace! 'ansatz.lean.jvm.ir
        '(ns ansatz.lean.jvm.ir (:import [java.lang.reflect Method]))))
  (doseq [form ['(ns ansatz.lean.jvm.ir (:require [prototype.machine :as m]))
                '(ns ansatz.lean.jvm.ir (:require [clojure.test :as t]))
                '(ns java-ir-baseline)
                '(ns ansatz.lean.jvm.ir (:require prototype.machine))
                '(ns ansatz.lean.jvm.ir (:use prototype.machine))
                '(ns ansatz.lean.jvm.ir (:import [ansatz.kernel Name]))]]
    (is (rejected? #(audit/check-namespace! 'ansatz.lean.jvm.ir form)))))
(def capture-text "package ansatz.research.ir;\npublic final class Interpreter {}\n")
;; Independent fixed fixture digest, not computed by the capture implementation.
(def capture-sha "17201026af9a47a21778efd2073c24ae04ba7f31203fd78b8376c3b128579345")
(defn with-capture-fixture [f]
  (let [parent (.toPath (io/file *module-root* "target/capture-checks"))]
    (Files/createDirectories parent (make-array java.nio.file.attribute.FileAttribute 0))
    (let [directory (.toFile (Files/createTempDirectory parent "capture-"
                              (make-array java.nio.file.attribute.FileAttribute 0)))]
      (try (f directory)
           (finally (doseq [file (reverse (file-seq directory))] (io/delete-file file)))))))
(deftest capture-freezes-only-the-pinned-source-despite-unlisted-neighbors
  (with-capture-fixture
    (fn [root]
      (let [source (io/file root "source/Interpreter.java")
            neighbor (io/file root "source/Unlisted.java")
            stage (io/file root "java-source")]
        (io/make-parents source)
        (spit source capture-text :encoding "UTF-8")
        (spit neighbor "deliberately invalid unlisted Java neighbor" :encoding "UTF-8")
        (let [captured (audit/capture-engine-source! source capture-sha stage)
              destination (io/file stage (:path captured))]
          (is (= capture-sha (:sha256 captured)))
          (is (= capture-text (slurp destination :encoding "UTF-8")))
          (is (= ["Interpreter.java"] (mapv #(.getName %) (filter #(.isFile %) (file-seq stage)))))
          ;; A later change to the canonical file cannot change compiler input.
          (spit source "mutated after capture" :encoding "UTF-8")
          (is (= capture-text (slurp destination :encoding "UTF-8"))))))))
(deftest changed-source-before-capture-does-not-publish-a-staged-input
  (with-capture-fixture
    (fn [root]
      (let [source (io/file root "Interpreter.java") stage (io/file root "java-source")]
        (spit source "mutated before capture" :encoding "UTF-8")
        (is (rejected? #(audit/capture-engine-source! source capture-sha stage)))
        (is (not (.exists stage)))))))

(defn check! [module-root]
  (binding [*module-root* module-root] (run-tests 'ansatz-lean-jvm-build-audit-checks)))
