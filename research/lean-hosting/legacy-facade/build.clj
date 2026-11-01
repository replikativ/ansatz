(ns build
  "Build ONLY the optional source-loaded module; never AOT prototype protocols."
  (:require [clojure.tools.build.api :as b]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [build-audit :as audit]))

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
        root (io/file "../src")]
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
    (audit/verify! closure root "src")
    (audit/verify-dependency! (edn/read-string (slurp "deps.edn")))
    closure))

(defn check-closure
  "Run the strict source inventory audit from the legacy facade without a core jar."
  [_]
  (let [closure (verify-closure! (edn/read-string (slurp "runtime-closure.edn")))]
    (println "Optional Lean runtime closure verified:" (count (:sources closure)) "sources")
    {:source-count (count (:sources closure))
     :resource-count (count (:resources closure))}))

(defn test-audit
  "Reader/inventory negative tests, without optional compiler/core namespaces."
  [_]
  (load-file "test/build_audit_test.clj")
  (let [result ((resolve 'build-audit-test/run-tests!))]
    (when-not (and (= 3 (:test result)) (zero? (+ (:fail result) (:error result))))
      (throw (ex-info "Optional package audit tests failed" result)))
    result))

(defn check-package
  "One tool JVM for the strict inventory and its negative audit contracts."
  [_]
  {:closure (check-closure {}) :audit-tests (test-audit {})})

(defn consumer-bases
  "Resolve isolated core-only and compiler consumer classpaths. Never append a
   different resolved closure: each output has one selected coordinate per lib."
  [{:keys [core-jar module-jar output-dir]}]
  (doseq [path [core-jar module-jar]]
    (when-not (and (string? path) (.isFile (io/file path)) (str/ends-with? path ".jar"))
      (throw (ex-info "Explicit existing consumer input jars required" {}))))
  (let [core (.getCanonicalPath (io/file core-jar))
        module (.getCanonicalPath (io/file module-jar))
        resolve-basis (fn [deps]
                        (let [basis (b/create-basis
                                     {:root nil :user nil :project nil
                                      :extra {:paths [] :deps deps
                                              :mvn/repos {"central" {:url "https://repo.maven.apache.org/maven2/"}
                                                          "clojars" {:url "https://repo.clojars.org/"}}}})
                              roots (:classpath-roots basis)]
                          (when-not (and (= (count roots) (count (set roots)))
                                         (every? #(and (.isFile (io/file %)) (str/ends-with? % ".jar")) roots))
                            (throw (ex-info "Consumer basis must contain unique jars only" {})))
                          {:jars roots :libs (update-vals (:libs basis) #(select-keys % [:mvn/version :local/root :paths]))}))
        default (resolve-basis {'org.replikativ/ansatz {:local/root core}})
        enabled (resolve-basis {'org.replikativ/ansatz {:local/root core}
                                'org.replikativ/ansatz-lean {:local/root module}})
        result {:schema "lean-consumer-bases/1" :configuration {:root nil :user nil :project nil}
                :pattern-profile :module-pom
                :default default :enabled enabled}]
    (.mkdirs (io/file output-dir))
    (spit (io/file output-dir "consumer-bases.edn") (pr-str result))
    (doseq [[label data] [[:default default] [:enabled enabled]]]
      (spit (io/file output-dir (str (name label) ".cp"))
            (str/join java.io.File/pathSeparator (:jars data))))
    (println "Isolated consumer jars:" {:default (count (:jars default)) :enabled (count (:jars enabled))})
    result))

(defn jar
  "Run from research/lean-hosting/legacy-facade. Requires an explicit pinned core jar and its actual
   Maven version; source-tree root classes are never accepted as the core basis.
   Example: clj -T:build jar :core-jar '\"../../../target/ansatz.jar\"'
            :core-version '\"0.2.<revision>\"'. No implicit deploy/publish."
  [{:keys [core-jar core-version version] :or {version "0.1.0-experimental"}}]
  (when-not (and (string? core-jar) (.isFile (io/file core-jar))
                 (str/ends-with? core-jar ".jar") (string? core-version) (seq core-version))
    (throw (ex-info "Explicit built pinned core-jar and core-version required" {})))
  (let [closure (verify-closure! (edn/read-string (slurp "runtime-closure.edn")))
        basis (b/create-basis {:project "deps.edn"
                               :extra {:deps {'org.replikativ/ansatz {:local/root core-jar}}}})
        ;; Published POM uses the pinned core Maven coordinate, not local paths.
        ;; Only declared module dependencies enter the POM, not CLI/tool defaults.
        pom-basis (assoc basis :libs {'org.replikativ/ansatz {:mvn/version core-version}
                                     'org.replikativ/pattern (select-keys audit/pattern-profile [:mvn/version])})]
    (b/delete {:path class-dir})
    (b/delete {:path jar-file})
    (b/copy-dir {:src-dirs ["src"] :target-dir class-dir})
    (doseq [path (concat (:sources closure) (:resources closure))]
      (let [source (io/file "../src" path)
            target (io/file class-dir path)]
        (io/make-parents target)
        (io/copy source target)))
    (let [target (io/file class-dir "META-INF/ansatz-lean/runtime-closure.edn")]
      (io/make-parents target)
      (io/copy (io/file "runtime-closure.edn") target))
    (b/javac {:src-dirs ["src-java"] :class-dir class-dir :basis basis
              :javac-opts ["--release" "11"]})
    (b/write-pom {:class-dir class-dir :lib lib :version version
                  :basis pom-basis :src-dirs ["src"]})
    (b/jar {:class-dir class-dir :jar-file jar-file})
    {:jar jar-file :core-version core-version :runtime-minimum 17
     :aot false :source-count (count (:sources closure))}))
