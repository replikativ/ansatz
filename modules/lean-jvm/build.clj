(ns build
  "Build the internal JVM adapter with its single authoritative Java engine.
   Native source producers remain outside the runtime JAR."
  (:require [clojure.tools.build.api :as b] [clojure.java.io :as io] [clojure.edn :as edn]
            [ansatz-lean-jvm-build-audit :as audit]
            [ansatz-lean-jvm-release :as release]))
(def lib 'org.replikativ/ansatz-lean-jvm)
(def class-dir "target/classes")
(def jar-file "target/ansatz-lean-jvm.jar")
(def java-source-dir "target/java-source")
(defn check-package [options] (audit/verify! options))
(defn coordinated-version
  "Same git-count version rule as the root build. Run from this module."
  []
  (format "0.2.%s" (b/git-count-revs {:dir "../.."})))

(defn jar
  "Producer build only, from modules/lean-jvm. Runtime dependencies use Maven
   coordinates. Consumers resolve the jar, never the research source directory."
  [{:keys [version]}]
  (let [version (release/check-version! (or version (coordinated-version)))
        {:keys [closure]} (check-package {})
        basis (b/create-basis {:project "deps.edn" :root nil :user nil})
        ;; Emit only the reviewed runtime coordinates, excluding build tooling.
        pom-basis (assoc basis :libs audit/runtime-dependencies)]
    (b/delete {:path java-source-dir})
    (audit/capture-java-sources! (concat (:java-engine closure) (:java-api closure)) java-source-dir)
    (b/delete {:path class-dir})
    (b/delete {:path jar-file})
    (b/copy-dir {:src-dirs ["src" "resources"] :target-dir class-dir})
    (let [metadata (io/file class-dir "META-INF/ansatz-lean-jvm/runtime.edn")]
      (spit metadata (pr-str (assoc (edn/read-string (slurp metadata)) :artifact-version version))))
    (b/javac {:src-dirs [java-source-dir] :class-dir class-dir :basis basis :javac-opts ["--release" "17"]})
    (audit/write-class-inventory! closure class-dir)
    (b/write-pom {:class-dir class-dir :lib lib :version version :basis pom-basis :src-dirs ["src"]
                  :scm {:url "https://github.com/replikativ/ansatz"
                        :connection "scm:git:git://github.com/replikativ/ansatz.git"
                        :developerConnection "scm:git:ssh://git@github.com/replikativ/ansatz.git"
                        :tag (str "v" version)}
                  :pom-data [[:description "Optional Ansatz Lean JVM interpreter runtime"]
                             [:url "https://github.com/replikativ/ansatz"]
                             [:licenses [:license [:name "Apache License 2.0"]
                                         [:url "https://www.apache.org/licenses/LICENSE-2.0"]]]]})
    (b/jar {:class-dir class-dir :jar-file jar-file})
    {:jar jar-file :version version :java-release 17 :engine-compilations 1
     :source-loaded-namespaces 1 :public-project-api (:public-project-api (edn/read-string (slurp (io/file class-dir "META-INF/ansatz-lean-jvm/runtime.edn"))))}))


(defn prepare-release
  "Build and identify the exact optional artifact/POM bytes. This does not deploy
   or assert public Project API readiness. Pass the root release's :version to
   keep independently built optional modules aligned with one release commit."
  [options]
  (let [result (jar options)
        pom-file (b/pom-path {:lib lib :class-dir class-dir})]
    (release/prepare! {:jar-file jar-file :pom-file pom-file
                       :version (:version result)
                       :output "target/release.edn"})))

(defn deploy-prepared
  "Explicit producer operation: verify an already reviewed release receipt,
   then deploy exactly those bytes to Clojars. Does not rebuild or choose a new
   version. This is not called by jar or prepare-release."
  [{:keys [receipt version] :or {receipt "target/release.edn"}}]
  (let [{:keys [jar-file pom-file] :as prepared}
        (release/verify! {:receipt receipt :version version})]
    ((requiring-resolve 'deps-deploy.deps-deploy/deploy)
     {:installer :remote :artifact jar-file :pom-file pom-file})
    prepared))
