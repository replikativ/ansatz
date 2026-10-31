(ns ansatz-lean-jvm-build-audit-checks
  "Source-only inventory/dependency gate; never loads the interpreter."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.edn :as edn] [clojure.java.io :as io]
            [ansatz-lean-jvm-build-audit :as audit]))
(def ^:dynamic *module-root* nil)
(defn rejected? [f] (try (f) false (catch clojure.lang.ExceptionInfo _ true)))
(defn closure [] (edn/read-string (slurp (io/file *module-root* "runtime-closure.edn"))))
(deftest actual-package-is-explicit-and-source-only
  (let [result (audit/verify! {:module-root *module-root*})]
    (is (= 1 (:sources result))) (is (= 1 (:resources result)))
    (is (= 1 (:java-sources result)))
    (is (= '{org.clojure/clojure {:mvn/version "1.12.0"}} (:runtime-dependencies result)))))
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
(defn check! [module-root]
  (binding [*module-root* module-root] (run-tests 'ansatz-lean-jvm-build-audit-checks)))
