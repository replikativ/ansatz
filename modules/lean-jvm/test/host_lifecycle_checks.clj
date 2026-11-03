(ns host-lifecycle-checks
  "Actual prepared-code failures must retire without retaining quarantined heaps."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io]
            [ansatz.lean.jvm.project :as project])
  (:import [ansatz.lean.jvm Lean HostBindings LeanException]
           [java.util.function Function]))

(def ^:dynamic *artifact* "consumer/resources/lean/pure-ffi.zip")
(def ^:private manifest "5f65bfb38748fd50ca24869a244af15dee933fe6454287d7c0d3b0426371bff4")
(defn- load-project [runtime bindings]
  (with-open [input (io/input-stream *artifact*)]
    (.loadArtifact ^Lean runtime input manifest bindings)))

(deftest actual-host-failures-retire-initializer-ordinary-and-native-worker-packets
  (let [before (count @@#'project/quarantine)
        failure (reify Function (apply [_ _] (throw (IllegalArgumentException. "host failure"))))]
    (with-open [runtime (Lean/open)]
      (doseq [[binding entry argument] [["Interop.normalize" nil nil]
                                       ["Interop.normalizeMessage" "Interop.process" (biginteger 41)]
                                       ["Interop.isA" "Interop.containsA" "abc"]]]
        (let [bindings (.build (.pure (HostBindings/builder) binding "failure/1" failure))]
          (try
            (with-open [project (load-project runtime bindings)]
              (when entry (.call project entry (object-array [argument])))
              (is false "Expected host failure"))
            (catch LeanException error (is (= "HostFailure" (.code error)))))
        (is (= before (count @@#'project/quarantine)))))
      (with-open [project (load-project runtime (HostBindings/empty))]
        (is (= (biginteger 7) (.call project "Interop.initialValue" (object-array [(biginteger 1)]))))))))

(defn check!
  ([] (run-tests 'host-lifecycle-checks))
  ([file] (binding [*artifact* file] (check!))))
