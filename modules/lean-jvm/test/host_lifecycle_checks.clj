(ns host-lifecycle-checks
  "Actual prepared-code failures must retire without retaining quarantined heaps."
  (:require [clojure.test :refer [deftest is run-tests]]
            [clojure.java.io :as io]
            [ansatz.lean.jvm.project :as project])
  (:import [ansatz.lean.jvm Lean HostBindings LeanException]
           [java.util.function Function]))

(def ^:dynamic *artifact* "consumer/resources/lean/pure-ffi.zip")
(def ^:private manifest "da1169a358c744b5c07eb4c68dd3a45b5e70638f8141b98f2f153e293ac457ac")
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

(deftest foreign-io-failures-retire-without-quarantine
  (let [before (count @@#'project/quarantine)
        file (io/file (.getParentFile (io/file *artifact*)) "foreign-ffi.zip")
        sha "860bed68ede444aca008e5e6fb570c86fe7a4248bda9cd7761d0b20f2dd9dfab"
        callback (reify Function (apply [_ _] (throw (IllegalStateException. "IO callback failed"))))]
    (with-open [runtime (Lean/open)]
      (let [bindings (-> (HostBindings/builder)
                         (.pure "HostInterop.length" "length/1" (reify Function (apply [_ _] (biginteger 0))))
                         (.pure "HostInterop.zero" "zero/1" (reify Function (apply [_ _] (biginteger 0))))
                         (.pureFactory "HostInterop.makeMessage" "message/1"
                                       (reify Function (apply [_ signature]
                                         (let [constructor (first (.constructors (.resultType signature)))]
                                           (reify Function (apply [_ args] (.create constructor args)))))))
                         (.io "HostInterop.readConfig" "failure/1" callback) (.build))]
        (with-open [input (io/input-stream file) project (.loadArtifact runtime input sha bindings)]
          (is (thrown-with-msg? LeanException #"Host implementation failed"
                               (.call project "HostInterop.describe" (object-array ["key"])))))
      (is (= before (count @@#'project/quarantine)))))))

(defn check!
  ([] (run-tests 'host-lifecycle-checks))
  ([file] (binding [*artifact* file] (check!))))
