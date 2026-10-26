(ns build
  "Build ONLY the optional source-loaded module; never AOT prototype protocols."
  (:require [clojure.tools.build.api :as b]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]))

(def lib 'org.replikativ/ansatz-lean)
(def class-dir "target/classes")
(def jar-file "target/ansatz-lean.jar")

(defn- namespace-path [namespace]
  (str (-> (str namespace) (str/replace "." "/") (str/replace "-" "_"))))

(defn verify-closure!
  "Audit selected source dependencies before staging. Additional dynamic resources
   must be listed separately and reviewed; this is not a bootstrap asset pack."
  [closure]
  (let [paths (set (:sources closure))
        root (io/file "../../experiments/lean-ir/src")]
    (when-not (= [] (:java closure))
      (throw (ex-info "Unaudited optional runtime Java helpers" {})))
    (doseq [path paths]
      (when-not (re-matches #"prototype/[a-z_]+\.cljc?" path)
        (throw (ex-info "Invalid closure source path" {:path path})))
      (let [source (slurp (io/file root path))
            dependencies (map second (re-seq #"\[(prototype\.[a-z0-9-]+)" source))]
        (doseq [dependency dependencies
                :let [stem (namespace-path dependency)]]
          (when-not (some paths [(str stem ".clj") (str stem ".cljc")])
            (throw (ex-info "Runtime source dependency absent from explicit closure"
                            {:source path :dependency dependency}))))))
    (doseq [path (:resources closure)]
      (when-not (= "prototype/runtime_signatures.edn" path)
        (throw (ex-info "Unaudited runtime resource" {:path path}))))
    closure))

(defn check-closure
  "Run the strict source inventory audit from modules/lean without a core jar."
  [_]
  (let [closure (verify-closure! (edn/read-string (slurp "runtime-closure.edn")))]
    (println "Optional Lean runtime closure verified:" (count (:sources closure)) "sources")
    {:source-count (count (:sources closure))
     :resource-count (count (:resources closure))}))

(defn jar
  "Run from modules/lean. Requires an explicit pinned core jar and its actual
   Maven version; source-tree root classes are never accepted as the core basis.
   Example: clj -T:build jar :core-jar '\"../../target/ansatz.jar\"'
            :core-version '\"0.2.<revision>\"'. No implicit deploy/publish."
  [{:keys [core-jar core-version version] :or {version "0.1.0-experimental"}}]
  (when-not (and (string? core-jar) (.isFile (io/file core-jar))
                 (str/ends-with? core-jar ".jar") (string? core-version) (seq core-version))
    (throw (ex-info "Explicit built pinned core-jar and core-version required" {})))
  (let [closure (verify-closure! (edn/read-string (slurp "runtime-closure.edn")))
        basis (b/create-basis {:project "deps.edn"
                               :extra {:deps {'org.replikativ/ansatz {:local/root core-jar}}}})
        ;; Published POM uses the pinned core Maven coordinate, not local paths.
        pom-basis (assoc-in basis [:libs 'org.replikativ/ansatz]
                            {:mvn/version core-version})]
    (b/delete {:path class-dir})
    (b/delete {:path jar-file})
    (b/copy-dir {:src-dirs ["src"] :target-dir class-dir})
    (doseq [path (concat (:sources closure) (:resources closure))]
      (let [source (io/file "../../experiments/lean-ir/src" path)
            target (io/file class-dir path)]
        (io/make-parents target)
        (io/copy source target)))
    (b/javac {:src-dirs ["src-java"] :class-dir class-dir :basis basis
              :javac-opts ["--release" "11"]})
    (b/write-pom {:class-dir class-dir :lib lib :version version
                  :basis pom-basis :src-dirs ["src"]})
    (b/jar {:class-dir class-dir :jar-file jar-file})
    {:jar jar-file :core-version core-version :runtime-minimum 17
     :aot false :source-count (count (:sources closure))}))
