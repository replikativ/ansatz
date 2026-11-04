(ns ansatz-lean-jvm-build-audit
  "Source-only package boundary audit. Does not load the adapter or Java engine."
  (:require [clojure.edn :as edn] [clojure.data.json :as json] [clojure.java.io :as io] [clojure.string :as str])
  (:import [java.nio.file Files StandardOpenOption] [java.security MessageDigest]))

(def engine-class "ansatz.lean.jvm.internal.exec.Interpreter")
(def runtime-resources ["META-INF/ansatz-lean-jvm/LakeInventory.lean"
                        "META-INF/ansatz-lean-jvm/runtime.edn"
                        "META-INF/ansatz-lean-jvm/user-error.json"
                        "META-INF/ansatz-lean-jvm/filesystem-layouts.jsonl"
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
                   (re-matches #"ansatz/lean/jvm/(?:[a-z_]+/)*[a-z_][a-z_0-9]*\.clj" path))
               (= path (namespace-path namespace))) "Runtime namespace/resource path mismatch"))
  (need (= (count (:sources closure)) (count (set (map :path (:sources closure))))) "Duplicate runtime source")
  (let [loaded (:source-loaded closure)]
    (need (and (vector? loaded) (every? symbol? loaded) (= (count loaded) (count (set loaded)))
               (every? (set (map :namespace (:sources closure))) loaded)
               (< (count loaded) (count (:sources closure))))
          "Explicit source-loaded namespace subset required"))
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

(def clojure-class-inventory-path "META-INF/ansatz-lean-jvm/clojure-classes.json")
(def java-class-inventory-path "META-INF/ansatz-lean-jvm/java-classes.json")
(defn clojure-aot-promise
  "Packaged metadata promise for the AOT namespaces: compiled against the audited
   runtime Clojure, without direct linking (calls stay Var-indirect)."
  []
  {:compiled-with (get-in runtime-dependencies ['org.clojure/clojure :mvn/version]) :direct-linking false})
(defn aot-namespaces
  "Every inventoried runtime namespace except the explicit source-loaded ones."
  [closure]
  (let [loaded (set (:source-loaded closure))]
    (vec (remove loaded (map :namespace (:sources closure))))))
(defn- namespace-root [value] (let [path (namespace-path value)] (subs path 0 (- (count path) 4))))
(defn check-aot-boundary!
  "An AOT namespace may not statically require a source-loaded one: its classes
   would bind deftypes/protocols the source load defines in another classloader."
  [closure forms]
  (let [loaded (set (:source-loaded closure))]
    (doseq [namespace (aot-namespaces closure)
            clause (drop 2 (get forms namespace)) :when (and (seq? clause) (= :require (first clause)))
            spec (rest clause)]
      (need (not (loaded (if (vector? spec) (first spec) spec)))
            (str "AOT namespace " namespace " requires a source-loaded namespace")))
    closure))

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

(defn- class-major-version [^bytes data]
  (need (and (<= 8 (alength data)) (= [0xca 0xfe 0xba 0xbe] (map #(bit-and 255 %) (take 4 data))))
        "Compiled class is not a class file")
  (bit-or (bit-shift-left (bit-and 255 (aget data 6)) 8) (bit-and 255 (aget data 7))))
(defn- contains-bytes? [^bytes data ^String needle]
  (.contains (String. data "ISO-8859-1") needle))
(defn class-namespace
  "Attribute one compiled class path to the AOT namespace whose compiler emits it:
   ns__init, ns$fn.., or a deftype/proxy/reify class in the namespace's package."
  [roots path]
  (let [base (subs path 0 (- (count path) 6))
        head (first (str/split base #"\$"))
        root (if (str/ends-with? head "__init") (subs head 0 (- (count head) 6)) head)
        parent (when (str/includes? root "/") (subs root 0 (str/last-index-of root "/")))]
    (or (get roots root) (when-not (str/ends-with? head "__init") (get roots parent)))))
(defn write-clojure-class-inventory!
  "Verify the assembled JAR directory and bind its AOT class bytes to the
   inventoried namespaces and their source bytes. AOT namespaces ship classes
   only; source-loaded namespaces ship their .clj only; no dependency classes."
  [closure jar-dir module-root clojure-version]
  (need (= clojure-version (:compiled-with (clojure-aot-promise))) "AOT Clojure differs from the audited runtime Clojure")
  (let [files (paths-under jar-dir)
        java-inventory (json/read-str (slurp (io/file jar-dir java-class-inventory-path)))
        java-classes (set (keys (get java-inventory "classes")))
        java-roots (set (map #(str (subs (:path %) 0 (- (count (:path %)) 5)))
                             (concat (:java-engine closure) (:java-api closure))))
        by-namespace (into {} (map (juxt :namespace identity) (:sources closure)))
        compiled (aot-namespaces closure)
        loaded (:source-loaded closure)
        roots (into {} (map (juxt namespace-root identity) compiled))
        classes (sort (remove java-classes (filter #(str/ends-with? % ".class") files)))
        attributed (into (sorted-map) (for [path classes] [path (class-namespace roots path)]))
        source-record (fn [namespace]
                        (let [{:keys [path]} (by-namespace namespace)]
                          {"namespace" (str namespace) "path" path
                           "sourceSHA256" (sha256 (io/file module-root "src" path))}))]
    (need (every? #(contains? files %) java-classes) "Packaged Java classes differ from their inventory")
    (doseq [path java-classes]
      (need (= (get-in java-inventory ["classes" path]) (sha256 (io/file jar-dir path))) "Packaged Java class bytes changed"))
    (need (every? some? (vals attributed)) "Compiled class outside the AOT namespaces (dependency or unreviewed class)")
    (need (not-any? #(contains? java-roots (first (str/split (subs % 0 (- (count %) 6)) #"\$"))) classes)
          "AOT class collides with an inventoried Java class")
    (need (= (set compiled) (set (vals attributed))) "AOT namespace emitted no classes")
    (doseq [namespace compiled]
      (need (contains? files (str (namespace-root namespace) "__init.class")) (str "Missing AOT init class for " namespace)))
    (doseq [path classes]
      (let [data (Files/readAllBytes (.toPath (io/file jar-dir path)))]
        (need (<= 52 (class-major-version data) 61) "AOT class is not loadable by Java 17")
        ;; The engine is reached only reflectively through ir/linked-basis.
        (need (not (contains-bytes? data "ansatz/lean/jvm/internal/")) "AOT class links an engine class directly")))
    (need (= (set (map #(:path (by-namespace %)) loaded))
             (set (filter #(str/ends-with? % ".clj") files))) "Packaged Clojure sources differ from the source-loaded inventory")
    (doseq [namespace loaded]
      (let [{:keys [path]} (by-namespace namespace)]
        (need (= (sha256 (io/file jar-dir path)) (sha256 (io/file module-root "src" path))) "Packaged Clojure source changed")))
    (let [inventory {"schema" "ansatz-clojure-class-inventory/1"
                     "clojureVersion" clojure-version "directLinking" false
                     "compiled" (mapv #(assoc (source-record %) "init" (str (namespace-root %) "__init.class")) compiled)
                     "sourceLoaded" (mapv source-record loaded)
                     "classes" (into (sorted-map) (for [[path namespace] attributed]
                                                    [path {"namespace" (str namespace) "sha256" (sha256 (io/file jar-dir path))}]))}
          destination (io/file jar-dir clojure-class-inventory-path)]
      (need (not (.exists destination)) "Clojure class inventory already present")
      (spit destination (json/write-str inventory))
      {:aot-namespaces (count compiled) :aot-classes (count classes) :source-loaded-namespaces (count loaded)})))

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
    (check-aot-boundary! closure
      (into {} (for [{:keys [path namespace]} (:sources closure)]
                 [namespace (check-namespace! namespace (source-ns (io/file root "src" path))
                                              (set (map :namespace (:sources closure)))
                                              (set (map :class (:java-api closure))))])))
    (need (= (:sha256 engine) (:engine-source-sha256 metadata) (sha256 java)) "Engine source/metadata pin mismatch")
    (need (= (:engine-closure-sha256 closure) (:engine-closure-sha256 metadata)) "Engine closure/metadata mismatch")
    (need (and (= "ansatz-lean-jvm-runtime/1" (:schema metadata)) (= 17 (:java-release metadata))
               (= "ansatz.lean.jvm.internal.exec.Interpreter" (:engine-class metadata))
               (= 'ansatz.lean.jvm.ir (:adapter-namespace metadata))
               (true? (:precompiled-engine metadata)) (false? (:runtime-java-compilation metadata))
               (false? (:native-compiler-included metadata)) (boolean? (:public-project-api metadata))
               (= (clojure-aot-promise) (:clojure-aot metadata)))
          "Unsupported package metadata promise")
    {:sources (count (:sources closure)) :resources (count (:resources closure))
     :aot-namespaces (count (aot-namespaces closure)) :source-loaded-namespaces (count (:source-loaded closure))
     :java-sources (+ (count (:java-engine closure)) (count (:java-api closure))) :engine-source-sha256 (:engine-source-sha256 metadata)
     :runtime-dependencies runtime-dependencies :closure closure}))

(defn repin!
  "Developer task: recompute the SHA-256 pins of every inventoried Java source and
   the engine closure, rewriting only the hash strings in runtime-closure.edn and
   the packaged runtime.edn. Adding or removing a Java source still requires
   editing the inventory by hand. Run from modules/lean-jvm, then `verify!`."
  [{:keys [module-root] :or {module-root "."}}]
  (let [root (io/file module-root)
        closure-file (io/file root "runtime-closure.edn")
        metadata-file (io/file root "resources/META-INF/ansatz-lean-jvm/runtime.edn")
        closure (edn/read-string (slurp closure-file))
        repinned (fn [sources]
                   (mapv #(assoc % :sha256 (sha256 (io/file root "src-java" (:path %)))) sources))
        engine' (repinned (:java-engine closure))
        api' (repinned (:java-api closure))
        closure-sha' (engine-closure-sha256 engine')
        engine-sha' (:sha256 (first (filter #(= engine-class (:class %)) engine')))
        replacements (into {(:engine-closure-sha256 closure) closure-sha'}
                           (map (fn [old new] [(:sha256 old) (:sha256 new)])
                                (concat (:java-engine closure) (:java-api closure)) (concat engine' api')))
        rewrite (fn [file pairs]
                  (let [text (slurp file)
                        text' (reduce-kv (fn [text old new]
                                           (need (or (= old new) (= 1 (count (re-seq (re-pattern old) text))))
                                                 (str "Pin is not unique in " file))
                                           (str/replace text old new)) text pairs)]
                    (when-not (= text text') (spit file text'))
                    (not= text text')))
        metadata (edn/read-string (slurp metadata-file))]
    {:closure-changed (rewrite closure-file replacements)
     :metadata-changed (rewrite metadata-file {(:engine-source-sha256 metadata) engine-sha'
                                               (:engine-closure-sha256 metadata) closure-sha'})
     :changed (vec (for [[old new] (map vector (concat (:java-engine closure) (:java-api closure)) (concat engine' api'))
                         :when (not= (:sha256 old) (:sha256 new))] (:path new)))}))
