(ns ansatz-lean-jvm-build-audit
  "Source-only package boundary audit. Does not load the adapter or Java engine."
  (:require [clojure.edn :as edn] [clojure.java.io :as io] [clojure.string :as str])
  (:import [java.nio.file Files] [java.security MessageDigest]))

(def engine-source "../../experiments/lean-ir/research/java-ir-baseline/src/ansatz/research/ir/Interpreter.java")
(def runtime-dependencies '{org.clojure/clojure {:mvn/version "1.12.0"}})
(defn- need [ok message] (when-not ok (throw (ex-info message {:audit :lean-jvm-package}))))
(defn- namespace-path [value] (str (str/replace (str/replace (str value) "." "/") "-" "_") ".clj"))
(defn validate-manifest! [closure]
  (need (= "ansatz-lean-jvm-source-closure/1" (:schema closure)) "Unknown closure schema")
  (need (and (vector? (:sources closure)) (seq (:sources closure))) "Explicit source inventory required")
  (doseq [{:keys [path namespace]} (:sources closure)]
    (need (and (symbol? namespace) (string? path)
               (re-matches #"ansatz/lean/jvm/[a-z_]+\.clj" path)
               (= path (namespace-path namespace))) "Runtime namespace/resource path mismatch"))
  (need (= (count (:sources closure)) (count (set (map :path (:sources closure))))) "Duplicate runtime source")
  (need (= ["META-INF/ansatz-lean-jvm/runtime.edn"] (:resources closure)) "Unknown runtime resource inventory")
  (need (and (= engine-source (get-in closure [:java :path]))
             (= "ansatz.research.ir.Interpreter" (get-in closure [:java :class]))
             (re-matches #"[0-9a-f]{64}" (or (get-in closure [:java :sha256]) "")))
        "Exactly the authoritative Interpreter source must be compiled")
  (need (= runtime-dependencies (:runtime-dependencies closure)) "Unexpected runtime dependency closure")
  closure)

(defn check-namespace! [expected form]
  (need (and (seq? form) (= 'ns (first form)) (= expected (second form))) "Source ns differs from inventory")
  (doseq [clause (drop 2 form) :when (seq? clause)]
    (need (#{:require :import :refer-clojure} (first clause)) "Unsupported runtime namespace loading clause")
    (case (first clause)
      :require (doseq [spec (rest clause)]
                 (need (and (vector? spec) (#{'clojure.java.io 'clojure.string 'clojure.edn} (first spec)))
                       "Research or undeclared dependency in packaged runtime namespace"))
      :import (doseq [spec (rest clause)]
                (need (str/starts-with? (str (if (vector? spec) (first spec) spec)) "java.")
                      "Non-JDK runtime import outside audited engine linkage"))
      :refer-clojure nil))
  form)
(defn- source-ns [file]
  (with-open [reader (java.io.PushbackReader. (io/reader file))]
    (binding [*read-eval* false] (read reader))))
(defn- paths-under [root]
  (if (.isDirectory (io/file root))
    (set (for [file (file-seq (io/file root)) :when (.isFile file)]
           (str/replace (str (.relativize (.toPath (io/file root)) (.toPath file))) "\\" "/"))) #{}))
(defn- sha256 [file]
  (let [bytes (Files/readAllBytes (.toPath (io/file file)))]
    (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") bytes)))))
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
    (doseq [{:keys [path namespace]} (:sources closure)]
      (check-namespace! namespace (source-ns (io/file root "src" path))))
    (need (= #{"Interpreter.java"} (paths-under (.getParentFile java))) "Extra Java source would be compiled")
    (need (= (get-in closure [:java :sha256]) (:engine-source-sha256 metadata) (sha256 java)) "Engine source/metadata pin mismatch")
    (need (and (= "ansatz-lean-jvm-runtime/1" (:schema metadata)) (= 17 (:java-release metadata))
               (= "ansatz.research.ir.Interpreter" (:engine-class metadata))
               (= 'ansatz.lean.jvm.ir (:adapter-namespace metadata))
               (true? (:precompiled-engine metadata)) (false? (:runtime-java-compilation metadata))
               (false? (:native-compiler-included metadata)) (false? (:public-project-api metadata)))
          "Unsupported package metadata promise")
    {:sources (count (:sources closure)) :resources (count (:resources closure))
     :java-sources 1 :engine-source-sha256 (:engine-source-sha256 metadata)
     :runtime-dependencies runtime-dependencies :closure closure}))
