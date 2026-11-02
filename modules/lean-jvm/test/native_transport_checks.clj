(ns ansatz-lean-jvm-native-transport-checks
  "Resource admission classification without launching any native process."
  (:require [clojure.test :refer [deftest is run-tests]]
            [ansatz.lean.jvm.compiler.transport :as transport]))
(defn- with-memory [kib f]
  (with-redefs-fn {#'transport/available-kib (constantly kib)} f))
(defn- failure [f] (try (f) nil (catch clojure.lang.ExceptionInfo error error)))
(deftest memory-floor-is-a-resource-refusal
  (doseq [running? [false true]]
    (let [error (with-memory 1234 #(failure (fn [] (#'transport/check-native-memory! running?))))]
      (is (= "ResourceLimit" (:code (ex-data error))))
      (is (= :host-memory (:resource (ex-data error))))
      (is (= 1234 (:available-kib (ex-data error))))
      (is (= (* 2 1024 1024) (:minimum-kib (ex-data error))))
      (is (re-find #"1234 KiB available" (.getMessage error)))))
  (is (nil? (with-memory (* 2 1024 1024) #(#'transport/check-native-memory! false)))))
(deftest preflight-refuses-before-process-arguments-or-directory-are-used
  (let [journal (atom {})
        error (with-memory 0 #(failure (fn [] (#'transport/run-process! {} journal nil nil nil nil))))]
    (is (= "ResourceLimit" (:code (ex-data error))))
    (is (re-find #"no native process started" (.getMessage error)))
    (is (empty? @journal))))
(deftest bridge-preserves-resource-code-through-native-journal-wrappers
  (let [resource (with-memory 42 #(failure (fn [] (#'transport/check-native-memory! false))))
        wrapper (ex-info "Native compilation failed; preserve compiler journal" {} resource)
        bridge (Class/forName "ansatz.lean.jvm.Bridge")
        method (.getDeclaredMethod bridge "failure" (into-array Class [Throwable]))]
    (.setAccessible method true)
    (let [projected (.invoke method nil (object-array [wrapper]))]
      (is (= "ResourceLimit" (.code ^ansatz.lean.jvm.LeanException projected)))
      (is (re-find #"42 KiB available" (.getMessage ^Throwable projected)))
      (is (nil? (.getCause ^Throwable projected))))))
(defn check! [] (run-tests 'ansatz-lean-jvm-native-transport-checks))
