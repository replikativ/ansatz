(ns ansatz-lean-jvm-build-audit
  "Source-only package boundary audit. Does not load the adapter or Java engine."
  (:require [clojure.edn :as edn] [clojure.data.json :as json] [clojure.java.io :as io] [clojure.string :as str])
  (:import [java.nio.file Files StandardOpenOption] [java.security MessageDigest]))

(def engine-class "ansatz.lean.jvm.internal.exec.Interpreter")
(def runtime-resources ["META-INF/ansatz-lean-jvm/runtime.edn"
                        "META-INF/ansatz-lean-jvm/user-error.json"
                        "META-INF/ansatz-lean-jvm/NOTICE"])
(def runtime-dependencies '{org.clojure/clojure {:mvn/version "1.12.0"}
                             org.clojure/data.json {:mvn/version "2.5.1"}})
(defn- need [ok message] (when-not ok (throw (ex-info message {:audit :lean-jvm-package}))))
(defn- namespace-path [value] (str (str/replace (str/replace (str value) "." "/") "-" "_") ".clj"))
(defn engine-closure-sha256 [sources]
  (let [text (apply str (for [{:keys [path class sha256]} (sort-by :path sources)]
                          (str path "\t" class "\t" sha256 "\n")))]
    (apply str (map #(format "%02x" (bit-and 255 %))
                   (.digest (MessageDigest/getInstance "SHA-256") (.getBytes text "UTF-8"))))))
(defn validate-manifest! [closure]
  (need (= "ansatz-lean-jvm-source-closure/2" (:schema closure)) "Unknown closure schema")
  (need (and (vector? (:sources closure)) (seq (:sources closure))) "Explicit source inventory required")
  (doseq [{:keys [path namespace]} (:sources closure)]
    (need (and (symbol? namespace) (string? path)
               (or (= "ansatz/lean/jvm.clj" path)
                   (re-matches #"ansatz/lean/jvm/(?:[a-z_]+/)*[a-z_]+\.clj" path))
               (= path (namespace-path namespace))) "Runtime namespace/resource path mismatch"))
  (need (= (count (:sources closure)) (count (set (map :path (:sources closure))))) "Duplicate runtime source")
  (need (= runtime-resources (:resources closure)) "Unknown runtime resource inventory")
  (need (and (= engine-class (:engine-class closure))
             (vector? (:java-engine closure)) (<= 1 (count (:java-engine closure)) 64)) "Explicit bounded engine source inventory required")
  (doseq [{:keys [path class sha256]} (:java-engine closure)]
    (need (and (string? path) (re-matches #"ansatz/lean/jvm/internal/(?:[a-z]+/)*[A-Z][A-Za-z0-9]*\.java" path)
               (= class (str/replace (subs path 0 (- (count path) 5)) "/" "."))
               (re-matches #"[0-9a-f]{64}" (or sha256 ""))) "Invalid engine source inventory"))
  (need (and (= 1 (count (filter #(= engine-class (:class %)) (:java-engine closure))))
             (= (engine-closure-sha256 (:java-engine closure)) (:engine-closure-sha256 closure))) "Engine source closure pin differs")
  (need (and (vector? (:java-api closure)) (seq (:java-api closure))) "Explicit Java API inventory required")
  (doseq [{:keys [path class sha256]} (:java-api closure)]
    (need (and (string? path) (re-matches #"ansatz/lean/jvm/[A-Z][A-Za-z0-9]*\.java" path)
               (= class (str/replace (subs path 0 (- (count path) 5)) "/" "."))
               (re-matches #"[0-9a-f]{64}" (or sha256 ""))) "Invalid Java API source inventory"))
  (need (= (count (:java-api closure)) (count (set (map :path (:java-api closure))))) "Duplicate Java API source")
  (let [sources (concat (:java-engine closure) (:java-api closure))]
    (need (= (count sources) (count (set (map :path sources))) (count (set (map :class sources)))) "Overlapping or duplicate Java source inventories"))
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
(defn capture-java-sources!
  "Capture the complete validated engine/API closure before writing any source.
   No neighboring files or classpath sources become compiler inputs."
  ([sources staging-root] (capture-java-sources! "." sources staging-root))
  ([module-root sources staging-root]
  (need (empty? (paths-under staging-root)) "Java source staging must be empty")
  (let [snapshots (mapv (fn [{:keys [path sha256]}]
                          (need (and (string? path) (re-matches #"ansatz/lean/jvm/(?:[a-z]+/)*[A-Z][A-Za-z0-9]*\.java" path)) "Contained Java source required")
                          (let [bytes (with-open [in (io/input-stream (io/file module-root "src-java" path))] (.readNBytes in 2097153))]
                            (need (<= (alength bytes) 2097152) "Java source exceeds bound")
                            (need (= sha256 (sha256-bytes bytes)) "Java source changed before capture")
                            {:path path :bytes bytes})) sources)]
    (need (<= (reduce + (map #(alength ^bytes (:bytes %)) snapshots)) 8388608) "Java source closure exceeds bound")
    (doseq [{:keys [path bytes]} snapshots]
      (let [destination (io/file staging-root path)]
        (io/make-parents destination)
        (Files/write (.toPath destination) ^bytes bytes
                     (into-array java.nio.file.OpenOption [StandardOpenOption/CREATE_NEW StandardOpenOption/WRITE]))))
    {:java-sources (count snapshots)})))
(defn write-class-inventory!
  "Bind exact compiled class bytes to the captured top-level source inventory."
  [closure class-dir]
  (let [sources (vec (concat (:java-engine closure) (:java-api closure)))
        roots (set (map #(str (subs (:path %) 0 (- (count (:path %)) 5)) ".class") sources))
        classes (sort (filter #(str/ends-with? % ".class") (paths-under class-dir)))
        top-level #(str (first (str/split % #"\$|\.class")) ".class")]
    (need (and (seq classes) (every? roots (map top-level classes))
               (every? (set classes) roots)) "Compiled classes do not match captured sources")
    (let [inventory {"schema" "ansatz-java-class-inventory/1"
                     "engineClosureSHA256" (:engine-closure-sha256 closure)
                     "sources" (mapv #(into {} (map (fn [[k v]] [(name k) v]) %)) sources)
                     "classes" (into (sorted-map) (map #(vector % (sha256 (io/file class-dir %))) classes))}
          destination (io/file class-dir "META-INF/ansatz-lean-jvm/java-classes.json")]
      (io/make-parents destination) (spit destination (json/write-str inventory))
      {:classes (count classes)})))

(defn verify!
  "Run from modules/lean-jvm or pass {:module-root path}. No JVM/backend effects."
  [{:keys [module-root] :or {module-root "."}}]
  (let [root (io/file module-root)
        closure (validate-manifest! (edn/read-string (slurp (io/file root "runtime-closure.edn"))))
        deps (edn/read-string (slurp (io/file root "deps.edn")))
        engine (first (filter #(= engine-class (:class %)) (:java-engine closure)))
        java (io/file root "src-java" (:path engine))
        metadata (edn/read-string (slurp (io/file root "resources/META-INF/ansatz-lean-jvm/runtime.edn")))]
    (need (= ["src" "resources" "target/classes"] (:paths deps)) "Runtime paths include development roots")
    (need (= runtime-dependencies (:deps deps)) "Module runtime deps differ from audited inventory")
    (need (= (set (map :path (:sources closure))) (paths-under (io/file root "src"))) "Uninventoried or absent runtime source")
    (need (= (set (:resources closure)) (paths-under (io/file root "resources"))) "Uninventoried or absent runtime resource")
    (need (= (set (map :path (concat (:java-engine closure) (:java-api closure)))) (paths-under (io/file root "src-java"))) "Uninventoried or absent Java API source")
    (doseq [{:keys [path] expected-sha :sha256} (concat (:java-engine closure) (:java-api closure))]
      (need (= expected-sha (sha256 (io/file root "src-java" path))) "Java API source pin differs"))
    (doseq [{:keys [path namespace]} (:sources closure)]
      (check-namespace! namespace (source-ns (io/file root "src" path))
                        (set (map :namespace (:sources closure)))
                        (set (map :class (:java-api closure)))))
    (need (= (:sha256 engine) (:engine-source-sha256 metadata) (sha256 java)) "Engine source/metadata pin mismatch")
    (need (= (:engine-closure-sha256 closure) (:engine-closure-sha256 metadata)) "Engine closure/metadata mismatch")
    (need (and (= "ansatz-lean-jvm-runtime/1" (:schema metadata)) (= 17 (:java-release metadata))
               (= "ansatz.lean.jvm.internal.exec.Interpreter" (:engine-class metadata))
               (= 'ansatz.lean.jvm.ir (:adapter-namespace metadata))
               (true? (:precompiled-engine metadata)) (false? (:runtime-java-compilation metadata))
               (false? (:native-compiler-included metadata)) (boolean? (:public-project-api metadata)))
          "Unsupported package metadata promise")
    {:sources (count (:sources closure)) :resources (count (:resources closure))
     :java-sources (+ (count (:java-engine closure)) (count (:java-api closure))) :engine-source-sha256 (:engine-source-sha256 metadata)
     :runtime-dependencies runtime-dependencies :closure closure}))
