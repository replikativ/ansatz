(ns ansatz-lean-jvm-artifact-models
  "Owner-free bounded ZIP/JSON/trust negatives; no synthetic native acceptance."
  (:require [clojure.test :refer [deftest is run-tests]] [ansatz.lean.jvm.artifact :as artifact])
  (:import [java.io ByteArrayInputStream ByteArrayOutputStream]
           [java.nio.charset StandardCharsets]
           [java.util.zip ZipOutputStream ZipEntry]))
(defn- bytes [s] (.getBytes ^String s StandardCharsets/UTF_8))
(defn- archive [entries]
  (let [output (ByteArrayOutputStream.)]
    (with-open [zip (ZipOutputStream. output StandardCharsets/UTF_8)]
      (doseq [[name data] entries]
        (.putNextEntry zip (ZipEntry. ^String name)) (.write zip ^bytes data 0 (alength ^bytes data)) (.closeEntry zip)))
    (.toByteArray output)))
(defn- rejected [data digest]
  (try (artifact/load! (ByteArrayInputStream. ^bytes data) digest) nil
       (catch clojure.lang.ExceptionInfo error (ex-data error))))
(deftest one-json-value-and-bounded-depth
  (is (= {} (#'artifact/strict-json! "{} \t\r\n")))
  (is (= {"text" "[]{}"} (#'artifact/strict-json! "{\"text\":\"[]{}\"}")))
  (doseq [bad ["{} {}" "{}garbage" "[]true" (str "{}" (char 11)) (str "{}" (char 0x2003))]]
    (is (thrown? Exception (#'artifact/strict-json! bad))))
  (is (thrown? Exception (#'artifact/strict-json! (str (apply str (repeat 257 "[")) "0" (apply str (repeat 257 "]")))))))
(deftest relative-path-contract
  (is (= "modules/project/Quoted.Module.lean" (#'artifact/relative! "modules/project/Quoted.Module.lean")))
  (doseq [path ["" "../outside" "a/../outside" "/absolute" "a//b" "a/./b" "a\\b" (str "a" (char 0))]]
    (is (thrown? clojure.lang.ExceptionInfo (#'artifact/relative! path)))))
(deftest zip-manifest-last-and-exact-case-sensitive-file-set
  (let [manifest (bytes "{}") digest (#'artifact/sha manifest)]
    (is (= :archive-file-set (:stage (rejected (archive [["manifest.json" manifest] ["later" (bytes "x")]]) digest))))
    (is (= :archive-file-set (:stage (rejected (archive [["a" (bytes "x")] ["A" (bytes "y")] ["manifest.json" manifest]]) digest))))
    (is (= :relative-path (:stage (rejected (archive [["../escape" (bytes "x")] ["manifest.json" manifest]]) digest))))
    (is (= :missing-manifest (:stage (rejected (archive [["payload" (bytes "x")]]) digest))))))
(deftest expected-hash-is-independent-and-verified-before-schema
  (let [manifest (bytes "{\"files\":{}}") data (archive [["manifest.json" manifest]])]
    (is (= :manifest-digest (:stage (rejected data (apply str (repeat 64 "0"))))))
    (is (= :artifact-profile (:stage (rejected data (#'artifact/sha manifest)))))
    (is (= :expected-manifest-digest (:stage (rejected data nil))))))
(deftest actual-uncompressed-admission-and-caller-stream-ownership
  (let [data (archive [["payload" (byte-array 100)] ["manifest.json" (bytes "{}")]])
        manifest-sha (#'artifact/sha (bytes "{}"))]
    (with-redefs [artifact/max-bytes 64]
      (is (= "BuildResourceLimit" (:code (rejected data manifest-sha))))))
  (let [closed (atom false) data (archive [["manifest.json" (bytes "{}")]])
        input (proxy [ByteArrayInputStream] [data] (close [] (reset! closed true)))]
    (is (thrown? clojure.lang.ExceptionInfo (artifact/load! input (apply str (repeat 64 "0")))))
    (is (false? @closed))))
(deftest exact-issued-artifact-identity-and-no-fake-source-export
  (let [consulted (atom false) foreign (proxy [Object] [] (hashCode [] (reset! consulted true) 17) (equals [_] true))]
    (is (thrown? clojure.lang.ExceptionInfo (artifact/authenticated-artifact foreign)))
    (is (false? @consulted)))
  (is (thrown? clojure.lang.ExceptionInfo (artifact/authenticated-artifact (ansatz.lean.jvm.artifact.ArtifactReceipt.))))
  (let [output (ByteArrayOutputStream.)]
    (is (thrown? clojure.lang.ExceptionInfo (artifact/export! {:accepted true} output)))
    (is (= 0 (.size output))))
  (is (thrown? clojure.lang.ExceptionInfo (#'artifact/canonical-bounded {"too" "large"} 1))))
(defn check! [] (run-tests 'ansatz-lean-jvm-artifact-models))
