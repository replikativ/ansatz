(ns ansatz.research.ir.native-project-loader
  "Definition loading only. No compiler process, artifact, engine or guest call."
  (:require [clojure.java.io :as io]))
(def directory (.getParentFile (io/file *file*)))
(defn load!
  ([] (load! directory))
  ([root]
   (when-not (find-ns 'java-ir-baseline) (throw (ex-info "Load Java IR basis definitions first" {})))
   (when (find-ns 'native-project-entry-v1)
     (throw (ex-info "Do not reload live native Artifact/Run registries" {})))
   (load-file (.getPath (io/file root "runner.clj")))
   {:scope :definitions-only :guest-calls 0}))
(defn load-models!
  ([] (load-models! directory))
  ([root]
   (when-not (find-ns 'native-project-entry-v1) (throw (ex-info "Load native entry definitions first" {})))
   (when (find-ns 'native-project-entry-models-v1) (throw (ex-info "Models already loaded" {})))
   (load-file (.getPath (io/file root "models.clj")))
   {:scope :model-definitions-only :guest-calls 0}))
(defn load-service!
  ([] (load-service! directory))
  ([root]
   (when-not (find-ns 'native-project-entry-v1) (throw (ex-info "Load native entry definitions first" {})))
   (when (find-ns 'native-project-service-v1) (throw (ex-info "Do not replace live configured Loaders" {})))
   (load-file (.getPath (io/file root "service.clj")))
   {:scope :service-definitions-only :compiler-processes 0 :guest-calls 0}))
(defn load-service-models!
  ([] (load-service-models! directory))
  ([root]
   (when-not (find-ns 'native-project-service-v1) (throw (ex-info "Load native service definitions first" {})))
   (when (find-ns 'native-project-service-models-v1) (throw (ex-info "Service models already loaded" {})))
   (load-file (.getPath (io/file root "service-models.clj")))
   {:scope :model-definitions-only :compiler-processes 0 :guest-calls 0}))
