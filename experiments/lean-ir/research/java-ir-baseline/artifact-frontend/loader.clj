(ns ansatz.research.ir.artifact-frontend-loader
  "Explicit definition loading only. Never starts a VM, guest call or source admission."
  (:require [clojure.java.io :as io]))
(def directory (.getParentFile (io/file *file*)))
(def prerequisites
  '[java-ir-baseline ansatz.research.ir.catalogue ansatz.research.ir.kernel-projection
    ansatz.research.ir.source-setup ansatz.research.ir.composite-source-v4 java-ir-module-data-graph])
(def units
  '[["authenticated-demand.clj" ansatz.research.ir.authenticated-demand]
    ["module.clj" java-matched-prelude-module-v4]
    ["lineage.clj" java-prelude-finalizer-lineage-v1]
    ["base.clj" java-matched-artifact-base-v1]
    ["authority.clj" artifact-declaration-authority-v4]
    ["adapter.clj" artifact-checked-declaration-adapter-v4]
    ["driver.clj" artifact-declaration-driver-v4]
    ["node-decoder.clj" ansatz.research.ir.node-decoder-v1]
    ["sequential-probe.clj" sequential-frontend-probe]
    ["options-proof.clj" heartbeat-lab-options-proof]
    ["imported-setup.clj" imported-frontend-setup-v4]
    ["generated-command.clj" generated-command-receipt-v1]
    ["filesystem-profile.clj" filesystem-nat-source-profile-v2]
    ["filesystem-provider.clj" filesystem-nat-source-provider-v2]
    ["filesystem-file.clj" filesystem-nat-file-run-v1]])
(def models
  '[["models/demand.clj" ansatz.research.ir.authenticated-demand-checks]
    ["models/lineage.clj" java-prelude-finalizer-lineage-models-v1]
    ["models/capability.clj" java-matched-prelude-capability-models-v4]
    ["models/authority.clj" artifact-declaration-authority-v4-models]
    ["models/adapter.clj" artifact-declaration-adapter-v4-models-v1]
    ["models/node-decoder.clj" ansatz.research.ir.node-decoder-checks-v1]
    ["models/generated-command.clj" generated-command-receipt-checks-v1]
    ["models/filesystem-profile.clj" filesystem-nat-source-profile-v2-checks]
    ["models/nat-arithmetic.clj" generated-nat-arithmetic-checks-v3]])
(defn- load-units! [root entries required]
  (doseq [n required]
    (when-not (find-ns n) (throw (ex-info "Load explicit research prerequisite first" {:namespace n}))))
  ;; Preflight the entire list before loading anything. Redefining deftypes or
  ;; opaque registries underneath live Run/Module/Base tokens is unsupported.
  (doseq [[path n] entries]
    (when (find-ns n) (throw (ex-info "Namespace already loaded; do not replace live research registries" {:namespace n})))
    (when-not (.isFile (io/file root path)) (throw (ex-info "Missing research definition file" {:file path}))))
  (doseq [[path _] entries] (load-file (.getPath (io/file root path))))
  {:scope :definitions-only :namespaces (mapv second entries) :guest-calls 0})
(defn load!
  "Load stable definitions once, after existing explicit research prerequisites.
   Does not open artifacts/stores, attach a resolver, build an engine or run tests."
  ([] (load! directory))
  ([root] (load-units! root units prerequisites)))
(defn load-models!
  "Load model definitions only; caller invokes each check! and binds decoder basis."
  ([] (load-models! directory))
  ([root] (load-units! root models
            (concat (map second units)
                    '[java-ir-baseline-checks java-ir-array-checks java-ir-pointer-checks java-ir-extern-checks]))))
