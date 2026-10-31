(ns ansatz.research.ir.runtime-cohort-loader
  "Explicit definitions/models only. Never opens a source/store, constructs an
   engine/image, installs a provider or runs tests. Existing opaque namespaces
   must not be replaced underneath live runtime capabilities."
  (:require [clojure.java.io :as io] [clojure.data.json :as json]))
(def directory (.getParentFile (io/file *file*)))
(def prerequisites
  '[java-ir-baseline lean-compatibility-corpus ansatz.research.ir.source-setup
    ansatz.research.ir.authenticated-demand sequential-frontend-probe imported-frontend-setup-v4
    java-matched-prelude-module-v4 java-prelude-finalizer-lineage-v1 java-matched-artifact-base-v1
    artifact-declaration-driver-v4 artifact-checked-declaration-adapter-v4
    generated-command-receipt-v1 heartbeat-lab-options-proof ansatz.export.storage])
(def required-vars '[java-ir-baseline/install-stdio-defaults! java-ir-baseline/start-dispose!])
(def units
  '[["native-init.clj" java-prelude-no-native-init]
    ["heartbeat-counter.clj" allocation-heartbeat-counter-v1]
    ["heartbeat-provider.clj" allocation-heartbeat-lab-v1]
    ["extern-bootstrap.clj" original-extern-bootstrap-v1]
    ["limits.clj" original-runtime-limits-provider-v1]
    ["row-cache.clj" authenticated-raw-row-cache-v1]
    ["cohort.clj" allocation-heartbeat-cohort-v1]
    ["stdin.clj" original-stdin-configuration-v1]])
(def models
  '[["models/heartbeat-counter.clj" allocation-heartbeat-counter-checks-v1]
    ["models/heartbeat-provider.clj" allocation-heartbeat-provider-checks-v1]
    ["models/router.clj" allocation-heartbeat-cohort-router-checks-v1]
    ["models/limits.clj" original-runtime-limits-provider-checks-v1]
    ["models/row-cache.clj" authenticated-raw-row-cache-checks-v1]
    ["models/extern-bootstrap.clj" original-extern-bootstrap-checks-v1]
    ["models/stdin.clj" original-stdin-configuration-checks-v1]])
(defn- sha-file [path]
  (with-open [input (io/input-stream path)]
    (let [digest (java.security.MessageDigest/getInstance "SHA-256") buffer (byte-array 65536)]
      (loop [] (let [n (.read input buffer)] (when (pos? n) (.update digest buffer 0 n) (recur))))
      (apply str (map #(format "%02x" (bit-and 255 %)) (.digest digest))))))
(defn- load-units! [root entries required]
  (doseq [n required]
    (when-not (find-ns n) (throw (ex-info "Load explicit research prerequisite first" {:namespace n}))))
  (let [manifest (json/read-str (slurp (io/file root "manifest.json")))]
    ;; Complete preflight before the first namespace/type/registry is defined.
    (doseq [[file n] entries]
      (when (find-ns n) (throw (ex-info "Namespace already loaded; do not replace live registries" {:namespace n})))
      (let [path (io/file root file) expected (get-in manifest ["files" file "sha256"])]
        (when-not (and (.isFile path) (string? expected) (= expected (sha-file path)))
          (throw (ex-info "Missing or changed reviewed definition file" {:file file}))))))
  (doseq [[file _] entries] (load-file (.getPath (io/file root file))))
  {:scope :definitions-only :namespaces (mapv second entries) :guest-calls 0})
(defn load!
  ([] (load! directory))
  ([root]
   (doseq [v required-vars]
     (when-not (and (find-ns (symbol (namespace v))) (find-var v)) (throw (ex-info "Load current stdio-capable baseline definitions first" {:var v}))))
   (load-units! root units prerequisites)))
(defn load-models!
  "Models define tests only. Run only with quiescent host/source activity, since
   model source callbacks use scoped with-redefs. Optional smoke! is NOT a test."
  ([] (load-models! directory))
  ([root] (load-units! root models (map second units))))
(defn load-missing-models!
  "Retained-REPL option: implementation namespaces must ALREADY be present.
   Load only missing model namespaces, skipping existing models without replacing
   Vars. Never loads implementation namespaces or redefines opaque registries."
  ([] (load-missing-models! directory))
  ([root]
   (let [missing (filterv (fn [[_ n]] (not (find-ns n))) models)
         skipped (mapv second (remove (set missing) models))
         result (load-units! root missing (map second units))]
     (assoc result :already-loaded-models skipped :implementation-namespaces-replaced 0))))
