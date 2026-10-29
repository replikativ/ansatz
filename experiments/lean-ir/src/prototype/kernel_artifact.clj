(ns prototype.kernel-artifact
  "Explicit provider-pinned kernel DATA admission, without kernel replay.
   This issuer admits one small reviewed fixture as a trusted assumption. It is
   not an Init release profile, strict verifier, runtime companion authentication,
   or frontend/provider implementation. Explicit association retains artifact provenance."
  (:require [prototype.module-store :as store]
            [prototype.imported-kernel :as kernel]
            [prototype.kernel-projection-snapshot :as snapshot]
            [prototype.helper-authority :as authority])
  (:import [ansatz.kernel Env ConstantInfo]
           [java.util WeakHashMap]))

(def native17-profile :native17ci-lean-4.33.1)
(def ^:private profiles
  {native17-profile
   {:sha256 "e6d3e40d1d1c00a3a4cbe98eb8642d6be5321b16ed18c8fbcdbc69028606c2f3"
    :lean-version "4.33.1" :lean-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
    :names #{"A" "aliasA" "hiddenA" "identityProof" "unsafeA"
             "Tiny" "Tiny.mk" "Tiny.rec" "Tiny.recOn"
             "Eq" "Eq.refl" "Eq.rec" "Eq.recOn"
             "Quot" "Quot.mk" "Quot.lift" "Quot.ind"}
    :quot-enabled? true}})

(deftype Admission [])
(def ^:private issued (WeakHashMap.))
(defn- require! [condition message data]
  (when-not condition (throw (ex-info message data))))

(defn- project [loaded profile-id profile]
  (let [world (:world loaded) source (:source loaded)
        _ (store/describe-attached world source)
        _ (require! (and (= (:sha256 profile) (:sha256 loaded) (:digest source))
                         (= (:lean-version profile) (get-in loaded [:manifest :input :leanVersion]))
                         (= (:lean-commit profile) (get-in loaded [:manifest :input :leanCommit])))
                    "Kernel artifact differs from the provider-owned profile" {:profile profile-id})
        entries (mapcat #(kernel/module-constants world %) (:roots loaded))
        indexed (reduce (fn [out {:keys [^ConstantInfo constant] :as entry}]
                          (let [name (.name constant)]
                            (require! (not (contains? out name))
                                      "Duplicate admitted kernel artifact name" {:name name})
                            (assoc out name entry))) {} entries)
        _ (require! (= (:names profile) (set (map str (keys indexed))))
                    "Kernel artifact does not have the exact provider-owned declaration inventory"
                    {:profile profile-id})
        projected (into {} (map (fn [[name entry]] [name (:constant entry)])) indexed)
        ;; Deliberately ADD existing ConstantInfos. No checkConstant, mutual /
        ;; inductive checking, verifier certificate, or guest-root association.
        environment (reduce (fn [^Env environment ^ConstantInfo ci] (.addConstant environment ci))
                            (Env.) (vals projected))
        environment (if (:quot-enabled? profile) (.enableQuot ^Env environment) environment)
        projection {:basis :trusted-artifact :profile profile-id
                    :provenance (select-keys profile [:sha256 :lean-version :lean-commit])
                    :base-assumptions
                    {:basis :trusted-artifact :declarations (set (keys indexed))
                     :axioms (set (for [[name ^ConstantInfo ci] projected :when (.isAxiom ci)] name))
                     :unsafe (set (for [[name ^ConstantInfo ci] projected
                                        :when (or (.isUnsafe ci)
                                                  (and (.isDef ci) (not= 0 (.safety ci))))] name))
                     :quot-enabled? (:quot-enabled? profile)}
                    :env environment :source source :roots (:roots loaded)
                    :constants (into {} (map (fn [[name entry]] [name (:guest entry)])) indexed)
                    :projected projected}]
    (let [projection (assoc projection :projection-sources [source])
          guard (snapshot/snapshot-projection projection)
          segment (select-keys guard [:projected :shapes :expression-arrays])]
      {:projection (assoc projection :java-guard-segments [segment]) :guard guard})))

(defn load-admitted
  "Open PATH using the provider's fixed SUPPORTED-ID/hash/inventory/Lean pins.
   There is no caller-supplied hash or registry. Returns actual :world/:roots,
   caller-owned newly opened :source, and an opaque in-process :admission token.
   The entire kernel base is explicitly trusted artifact data, not kernel
   checked. It installs no guest association. Only this operation's Store is
   closed on failure; pre-existing caller Stores remain caller-owned."
  [world supported-id path]
  (let [profile (get profiles supported-id)
        _ (require! profile "Unsupported provider-owned kernel artifact profile" {:profile supported-id})
        loaded (store/load-file world path {:sha256 (:sha256 profile) :max-nodes 516
                                           :max-bytes 1048576 :cache-size 64 :max-row-bytes 65536})
        source (:source loaded)]
    (try
      (let [admission (Admission.)
            record (project loaded supported-id profile)
            result {:world (:world loaded) :roots (:roots loaded) :source source :admission admission}]
        (locking issued (.put issued admission record))
        result)
      (catch Throwable cause
        (try (.close ^java.io.Closeable source)
             (catch Throwable cleanup (.addSuppressed cause cleanup)))
        (throw cause)))))

(defn inspect-for-world
  "Borrow an issued artifact projection only in a world with its exact open
   source attached once, no overlap/shadow, and unchanged eager Java CI domain,
   checking shapes, and expression universe arrays. Caller retains Store/root
   owners and serializes operations against Java mutation. Closing the Store
   invalidates inspection. Returned :basis/:base-assumptions retain the trusted
   artifact boundary; neither this map nor its Env is a strict certificate."
  [world token]
  (let [{:keys [projection guard] :as record} (locking issued (.get issued token))]
    (require! record "An issued in-process kernel artifact admission is required" {})
    (let [attached (store/describe-attached world (:source projection))]
      (require! (= (:roots projection) (:roots attached)) "Kernel artifact roots changed" {}))
    (snapshot/validate-projection guard)
    ;; Keep the registry value token-free so it cannot retain its own weak key.
    (assoc projection :kernel-provenance
           {:base-basis :trusted-artifact :artifact-admission token
            :base-assumptions (:base-assumptions projection)})))

(defn associate-admitted-progress
  "Associate actual guest Environment with exactly this issued artifact's CIs.
   Current independent helper authority is required. Revalidate token/source,
   original Java witnesses and helper identities across the actual helper
   boundary before publishing explicit artifact provenance. No strict order or
   verifier certificate is fabricated; failures retain the core owner packet."
  [context world environment helpers admission]
  (let [projection (inspect-for-world world admission)
        roots (cond-> (mapv helpers [:root :constants :quot-init?])
                (:constant-map helpers) (conj (:constant-map helpers)))
        code (authority/capture context world roots)
        validate (fn [world]
                   (inspect-for-world world admission)
                   (authority/check context world roots code)
                   (snapshot/validate-segments (:env projection) (:java-guard-segments projection)))]
    (kernel/associate-projection-progress context world environment helpers projection validate)))
