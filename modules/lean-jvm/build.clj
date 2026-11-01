(ns build
  "Build the internal JVM adapter with its single authoritative Java engine.
   No native compiler, runtime compilation, public project API or publication."
  (:require [clojure.tools.build.api :as b] [clojure.java.io :as io] [clojure.edn :as edn]
            [ansatz-lean-jvm-build-audit :as audit]))
(def lib 'org.replikativ/ansatz-lean-jvm)
(def class-dir "target/classes")
(def jar-file "target/ansatz-lean-jvm.jar")
(def java-source-dir "target/java-source")
(defn check-package [options] (audit/verify! options))
(defn jar
  "Producer build only, from modules/lean-jvm. Runtime dependencies use Maven
   coordinates. Consumers resolve the jar, never the research source directory."
  [{:keys [version] :or {version "0.1.0-experimental"}}]
  (let [{:keys [closure]} (check-package {})
        basis (b/create-basis {:project "deps.edn" :root nil :user nil})
        ;; Emit only the reviewed runtime coordinates, excluding build tooling.
        pom-basis (assoc basis :libs audit/runtime-dependencies)]
    (b/delete {:path java-source-dir})
    (audit/capture-engine-source! (get-in closure [:java :path])
                                  (get-in closure [:java :sha256]) java-source-dir)
    (b/delete {:path class-dir})
    (b/delete {:path jar-file})
    (b/copy-dir {:src-dirs ["src" "resources"] :target-dir class-dir})
    (let [metadata (io/file class-dir "META-INF/ansatz-lean-jvm/runtime.edn")]
      (spit metadata (pr-str (assoc (edn/read-string (slurp metadata)) :artifact-version version))))
    (b/javac {:src-dirs [java-source-dir] :class-dir class-dir :basis basis :javac-opts ["--release" "17"]})
    (b/write-pom {:class-dir class-dir :lib lib :version version :basis pom-basis :src-dirs ["src"]})
    (b/jar {:class-dir class-dir :jar-file jar-file})
    {:jar jar-file :version version :java-release 17 :engine-compilations 1
     :source-loaded-namespaces 1 :public-project-api false}))
