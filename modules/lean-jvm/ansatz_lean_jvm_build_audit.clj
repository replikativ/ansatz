(ns ansatz-lean-jvm-build-audit
  "Source-only package boundary audit. Does not load the adapter or Java engine."
  (:require [clojure.edn :as edn] [clojure.java.io :as io] [clojure.string :as str])
  (:import [java.nio.file Files StandardOpenOption] [java.security MessageDigest]))

(def engine-source "src-java/ansatz/lean/jvm/internal/exec/Interpreter.java")
(def runtime-resources ["META-INF/ansatz-lean-jvm/runtime.edn"
                        "META-INF/ansatz-lean-jvm/user-error.json"
                        "META-INF/ansatz-lean-jvm/NOTICE"])
(def runtime-dependencies '{org.clojure/clojure {:mvn/version "1.12.0"}
                             org.clojure/data.json {:mvn/version "2.5.1"}})
(defn- need [ok message] (when-not ok (throw (ex-info message {:audit :lean-jvm-package}))))
(defn- namespace-path [value] (str (str/replace (str/replace (str value) "." "/") "-" "_") ".clj"))
(defn validate-manifest! [closure]
  (need (= "ansatz-lean-jvm-source-closure/1" (:schema closure)) "Unknown closure schema")
  (need (and (vector? (:sources closure)) (seq (:sources closure))) "Explicit source inventory required")
  (doseq [{:keys [path namespace]} (:sources closure)]
    (need (and (symbol? namespace) (string? path)
               (or (= "ansatz/lean/jvm.clj" path)
                   (re-matches #"ansatz/lean/jvm/(?:[a-z_]+/)*[a-z_]+\.clj" path))
               (= path (namespace-path namespace))) "Runtime namespace/resource path mismatch"))
  (need (= (count (:sources closure)) (count (set (map :path (:sources closure))))) "Duplicate runtime source")
  (need (= runtime-resources (:resources closure)) "Unknown runtime resource inventory")
  (need (and (= engine-source (get-in closure [:java :path]))
             (= "ansatz.lean.jvm.internal.exec.Interpreter" (get-in closure [:java :class]))
             (re-matches #"[0-9a-f]{64}" (or (get-in closure [:java :sha256]) "")))
        "Exactly the authoritative Interpreter source must be compiled")
  (need (and (vector? (:java-api closure)) (seq (:java-api closure))) "Explicit Java API inventory required")
  (doseq [{:keys [path class sha256]} (:java-api closure)]
    (need (and (string? path) (re-matches #"ansatz/lean/jvm/[A-Z][A-Za-z0-9]*\.java" path)
               (= class (str/replace (subs path 0 (- (count path) 5)) "/" "."))
               (re-matches #"[0-9a-f]{64}" (or sha256 ""))) "Invalid Java API source inventory"))
  (need (= (count (:java-api closure)) (count (set (map :path (:java-api closure))))) "Duplicate Java API source")
  (need (= runtime-dependencies (:runtime-dependencies closure)) "Unexpected runtime dependency closure")
  closure)

(defn check-namespace!
  ([expected form] (check-namespace! expected form #{}))
  ([expected form runtime-namespaces] (check-namespace! expected form runtime-namespaces #{}))
  ([expected form runtime-namespaces api-classes]
  (need (and (seq? form) (= 'ns (first form)) (= expected (second form))) "Source ns differs from inventory")
  (doseq [clause (drop 2 form) :when (seq? clause)]
    (need (#{:require :import :refer-clojure} (first clause)) "Unsupported runtime namespace loading clause")
    (case (first clause)
      :require (doseq [spec (rest clause)]
                 (need (and (vector? spec) (contains? (into #{'clojure.java.io 'clojure.string 'clojure.edn 'clojure.data.json} runtime-namespaces) (first spec)))
                       "Research or undeclared dependency in packaged runtime namespace"))
      :import (doseq [spec (rest clause)]
                (let [classes (if (vector? spec) (map #(str (first spec) "." %) (rest spec)) [(str spec)])]
                  (doseq [class classes]
                    (need (or (str/starts-with? class "java.") (contains? api-classes class))
                          "Non-JDK runtime import outside inventoried Java API"))))
      :refer-clojure nil))
  form))
(defn- source-ns [file]
  (with-open [reader (java.io.PushbackReader. (io/reader file))]
    (binding [*read-eval* false] (read reader))))
(defn- paths-under [root]
  (if (.isDirectory (io/file root))
    (set (for [file (file-seq (io/file root)) :when (.isFile file)]
           (str/replace (str (.relativize (.toPath (io/file root)) (.toPath file))) "\\" "/"))) #{}))
(defn- sha256-bytes [bytes]
  (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") bytes))))
(defn- sha256 [file] (sha256-bytes (Files/readAllBytes (.toPath (io/file file)))))
(defn capture-engine-source!
  "Producer-only capture of one exact hash-checked byte array. Never scans or
   copies source neighbors. STAGING-ROOT must have no files; the build cleans only
   its owned target/java-source tree. No destination is written on pin failure."
  [source expected-sha staging-root]
  (let [maximum (* 2 1024 1024)
        bytes (with-open [input (Files/newInputStream (.toPath (io/file source))
                                  (make-array java.nio.file.OpenOption 0))]
                (.readNBytes input (int (inc maximum))))
        actual-sha (sha256-bytes bytes)
        relative "ansatz/lean/jvm/internal/exec/Interpreter.java"
        destination (io/file staging-root relative)]
    (need (<= (alength bytes) maximum) "Engine source capture exceeds bound")
    (need (= expected-sha actual-sha) "Engine source changed before capture")
    (need (empty? (paths-under staging-root)) "Engine source staging must be empty")
    (io/make-parents destination)
    (Files/write (.toPath destination) bytes
                 (into-array java.nio.file.OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))
    {:path relative :bytes (alength bytes) :sha256 actual-sha}))
(defn capture-api-sources!
  "Capture only pinned inventoried Java API source bytes into owned staging."
  [sources staging-root]
  (doseq [{:keys [path sha256]} sources]
    (need (and (string? path) (re-matches #"ansatz/lean/jvm/[A-Z][A-Za-z0-9]*\.java" path)
               (re-matches #"[0-9a-f]{64}" (or sha256 ""))) "Pinned contained Java API source required")
    (let [destination (io/file staging-root path)
          bytes (with-open [input (io/input-stream (io/file "src-java" path))]
                  (.readNBytes input 1048577))]
      (need (<= (alength bytes) 1048576) "Java API source exceeds bound")
      (need (= sha256 (sha256-bytes bytes)) "Java API source changed before capture")
      (io/make-parents destination)
      (Files/write (.toPath destination) bytes
                   (into-array java.nio.file.OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))))
  {:java-api-sources (count sources)})
(defn verify!
  "Run from modules/lean-jvm or pass {:module-root path}. No JVM/backend effects."
  [{:keys [module-root] :or {module-root "."}}]
  (let [root (io/file module-root)
        closure (validate-manifest! (edn/read-string (slurp (io/file root "runtime-closure.edn"))))
        deps (edn/read-string (slurp (io/file root "deps.edn")))
        java (io/file root engine-source)
        metadata (edn/read-string (slurp (io/file root "resources/META-INF/ansatz-lean-jvm/runtime.edn")))]
    (need (= ["src" "resources" "target/classes"] (:paths deps)) "Runtime paths include development roots")
    (need (= runtime-dependencies (:deps deps)) "Module runtime deps differ from audited inventory")
    (need (= (set (map :path (:sources closure))) (paths-under (io/file root "src"))) "Uninventoried or absent runtime source")
    (need (= (set (:resources closure)) (paths-under (io/file root "resources"))) "Uninventoried or absent runtime resource")
    (need (= (set (map :path (:java-api closure))) (paths-under (io/file root "src-java"))) "Uninventoried or absent Java API source")
    (doseq [{:keys [path] expected-sha :sha256} (:java-api closure)]
      (need (= expected-sha (sha256 (io/file root "src-java" path))) "Java API source pin differs"))
    (doseq [{:keys [path namespace]} (:sources closure)]
      (check-namespace! namespace (source-ns (io/file root "src" path))
                        (set (map :namespace (:sources closure)))
                        (set (map :class (:java-api closure)))))
    (need (= (get-in closure [:java :sha256]) (:engine-source-sha256 metadata) (sha256 java)) "Engine source/metadata pin mismatch")
    (need (and (= "ansatz-lean-jvm-runtime/1" (:schema metadata)) (= 17 (:java-release metadata))
               (= "ansatz.lean.jvm.internal.exec.Interpreter" (:engine-class metadata))
               (= 'ansatz.lean.jvm.ir (:adapter-namespace metadata))
               (true? (:precompiled-engine metadata)) (false? (:runtime-java-compilation metadata))
               (false? (:native-compiler-included metadata)) (boolean? (:public-project-api metadata)))
          "Unsupported package metadata promise")
    {:sources (count (:sources closure)) :resources (count (:resources closure))
     :java-sources (inc (count (:java-api closure))) :engine-source-sha256 (:engine-source-sha256 metadata)
     :runtime-dependencies runtime-dependencies :closure closure}))
