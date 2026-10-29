(ns prototype.checked-delta
  "Live checked-base and explicitly artifact-relative delta checking.
   Artifact authority comes only from the separate pinned issuer.
   Capture has the same TRUSTED in-process verifier-certificate and authorized
   helper-invoker contract as imported/associate-checked. Data equality alone
   never manufactures a capability. Strict verification remains unchanged."
  (:require [clojure.set :as set]
            [prototype.machine :as m]
            [prototype.native-scalar :as native]
            [prototype.native-heap :as heap]
            [prototype.module-store]
            [prototype.kernel-bridge :as bridge]
            [prototype.imported-kernel :as imported]
            [prototype.helper-authority :as authority]
            [prototype.kernel-projection-snapshot :as snapshot]
            [prototype.kernel-artifact :as artifact]
            [prototype.kernel-host :as kernel-host]
            [ansatz.kernel.env :as env])
  (:import [ansatz.kernel Env ConstantInfo TypeChecker]
           [java.util WeakHashMap]))

(deftype CheckedBase [])
(def ^:private issued (WeakHashMap.))
(def ^:dynamic ^:private *operation* nil)
(defn- stage! [stage] (when *operation* (vreset! (:stage *operation*) stage)))
(defn- publish! [world]
  (when *operation* (vreset! (:checkpoint *operation*) world)) world)
(defn- temporary! [owners]
  (when *operation* (vreset! (:temporary-owners *operation*) owners)))
(defn- operation [world thunk]
  (let [progress {:checkpoint (volatile! world) :stage (volatile! :preflight)
                  :temporary-owners (volatile! [])}]
    (binding [*operation* progress]
      (try (thunk)
           (catch Throwable cause
             (throw (ex-info (or (.getMessage cause) "Checked delta operation failed")
                             (merge {:checkpoint @(:checkpoint progress) :stage @(:stage progress)
                                     :temporary-owners @(:temporary-owners progress)}
                                    (ex-data cause)) cause)))))))
(defn- require! [condition message data]
  (when-not condition (throw (ex-info message data))))
(defn- sources! [world expected]
  (let [sources (vec (:native-imports world))]
    (require! (and (<= (count sources) 1)
                   (every? #(instance? prototype.module_store.Store %) sources))
              "Checked delta supports eager data or one verified Store" {})
    (when expected
      (require! (and (= (count sources) (count expected))
                     (every? true? (map identical? sources expected)))
                "Checked base source identity changed" {}))
    (doseq [source sources]
      (require! (false? @(:closed source)) "Checked base source lease is closed" {})
      (require! (not-any? #(heap/contains-id? source %) (keys (:heap world)))
                "Checked base source is shadowed" {}))
    sources))

(defn- eager-domain! [certificate]
  (snapshot/validate-eager-domain certificate))

(defn- authority-code! [context world roots expected]
  (authority/check context world roots expected))

(defn- helper-code! [context world helpers expected]
  (doseq [key [:root :constants :quot-init?]]
    (require! (vector? (get helpers key)) "Missing checked base helper" {:helper key}))
  (authority-code! context world (mapv helpers [:root :constants :quot-init?]) expected))

(defn validate-helper-authority
  "Validate explicit helper targets and their executable dependency closures
   against CURRENT independent function/binding registries before guest entry.
   This checks invocation authority only; it issues no checked-base capability."
  [context world roots]
  (authority-code! context world roots nil)
  nil)

(defn- read-environment
  "The caller's trusted invoker borrows Environment; helper outputs are owned."
  [context world environment helpers constants?]
  (let [progress (volatile! world) owners (volatile! [])
        invoke (fn [key]
                 (stage! [:helper key])
                 (let [[next value] ((:invoke context) @progress (get helpers key) [environment])]
                   (vreset! progress next) (publish! next)
                   (vswap! owners conj value) (temporary! @owners) value))]
    (try
      (let [root (invoke :root) _ (require! (m/ref? root) "Invalid checked guest root" {})
            _ (m/node @progress root)
            quot (invoke :quot-init?)
            quot (native/nat-value {:ref? m/ref? :node m/node} @progress quot)
            _ (require! (contains? #{0 1} quot) "Invalid checked quotient flag" {})
            values (when constants?
                     (let [array (invoke :constants) node (when (m/ref? array) (m/node @progress array))]
                       (require! (and (= :array (:kind node)) (vector? (:fields node)))
                                 "Invalid checked ConstantInfo enumeration" {})
                       (:fields node)))]
        (doseq [value @owners]
          (stage! :helper-release)
          (vreset! progress (m/release @progress value 1))
          (publish! @progress) (vswap! owners #(vec (rest %))) (temporary! @owners))
        [@progress root (= 1 quot) values])
      (catch Throwable cause
        (throw (ex-info "Checked guest helper failed"
                        (merge {:checkpoint @progress} (ex-data cause)
                               {:checked-delta-helper-owners @owners
                                :temporary-owners (into (vec @owners) (:temporary-owners (ex-data cause)))})
                        cause))))))

(defn- entries [world values certificate]
  (#'imported/project-entries world values certificate))
(defn- indexed! [entries]
  (reduce (fn [out {:keys [guest ^ConstantInfo constant] :as entry}]
            (let [name (.name constant)]
              (require! (not (contains? out name)) "Duplicate final ConstantInfo name" {:name name})
              (assoc out name entry))) {} entries))
(defn- same-base! [base indexed]
  (doseq [[name guest] (:constants base)]
    (let [entry (get indexed name)]
      (require! (and entry (= guest (:guest entry))) "Missing or replaced checked base reference" {:name name})
      (require! (= (get (:shapes base) name) (imported/checking-shape (:constant entry)))
                "Inherited ConstantInfo checking shape changed" {:name name}))))

(defn- expression-array-witnesses [certificate]
  (snapshot/expression-array-witnesses certificate))

(defn- current-java-base! [certificate]
  (snapshot/validate-projection certificate)
  nil)

(defn ^:no-doc snapshot-projection
  "Capture mutable Java containers in a complete eager projection.
   This is correspondence evidence only: it grants no checking or artifact
   admission authority. The owning host prevents concurrent mutation."
  [projection]
  (snapshot/snapshot-projection projection))

(defn ^:no-doc validate-projection
  "Compare actual eager Java objects with captured container snapshots.
   Does not authenticate the projection or establish checking history."
  [projection]
  (snapshot/validate-projection projection))

(defn- capture-base*
  "Issue [latest-world opaque-live-capability] from an EXISTING positive anchor.
   CERTIFICATE must be the actual trusted in-process strict-verifier result;
   this API does not authenticate arbitrary maps/EDN or assert checking history.
   CONTEXT invokes identity-authorized HELPERS, as associate-checked requires;
   :trusted-functions is its independently admitted helper closure registry.
   Raw helper bindings require matching :bindings/:trusted-bindings identities.
   The host retains all guest roots/source leases; this capability borrows them."
  [context world environment helpers certificate]
  (stage! :capture-certificate)
  (require! (not (or (= :trusted-artifact (:basis certificate))
                     (= :trusted-artifact (get-in certificate [:kernel-provenance :base-basis]))))
            "Strict base capture rejects artifact kernel provenance" {})
  (eager-domain! certificate)
  (require! (fn? (:invoke context)) "Authorized helper invoker required" {})
  (let [sources (sources! world nil) code (helper-code! context world helpers nil)
        [world root quot? values] (read-environment context world environment helpers true)
        _ (stage! :capture-association)
        anchor (get-in world [:kernel-environments (:id root)])
        checked (:env certificate)
        _ (require! (not= :trusted-artifact (get-in anchor [:kernel-provenance :base-basis]))
                    "Strict base capture rejects artifact kernel provenance" {})
        _ (require! (and (= root (:anchor anchor)) (identical? checked (:env anchor)))
                    "Existing positive checked association required" {})
        _ (require! (= quot? (.isQuotEnabled ^Env checked)) "Checked base quotient correspondence changed" {})
        _ (stage! :capture-projection)
        indexed (indexed! (entries world values certificate))
        base (snapshot-projection (assoc certificate :kernel-provenance {:base-basis :strict-fresh}))
        base (assoc base :java-guard-segments [(select-keys base [:projected :shapes :expression-arrays])])
        _ (require! (= (set (keys indexed)) (set (keys (:constants certificate))))
                    "Guest enumeration differs from complete checked base" {})
        _ (same-base! base indexed)
        _ (sources! world sources) _ (helper-code! context world helpers code)
        cap (CheckedBase.)]
    (locking issued
      (.put issued cap {:basis :strict-fresh :certificate base :sources sources :environment environment
                        :helpers helpers :helper-code code :root root :quot? quot?
                        :anchor (select-keys anchor [:anchor :env :constant-map :quot-init? :kernel-provenance :java-guard-segments])}))
    [world cap]))

(defn- policy! [world entries {:keys [allow-axioms? allow-compiler-markers? allow-unsafe?]}]
  (doseq [{:keys [guest ^ConstantInfo constant]} entries]
    (let [marker? (and allow-compiler-markers? (bridge/compiler-marker-declaration? world guest))]
      (require! (or (not (.isAxiom constant)) marker? allow-axioms?)
                "New axiom requires explicit host policy" {:name (.name constant)})
      (require! (or (not (or (.isUnsafe constant) (and (.isDef constant) (not= 0 (.safety constant)))))
                    marker? allow-unsafe?)
                "New unsafe/partial declaration requires explicit host policy" {:name (.name constant)}))))

(defn- verify-extension*
  "Check ONLY new declarations against an issued live eager checked base.
   VALUES must be the actual complete final guest CI enumeration. Every base
   name/ref is required; local/mutable inherited graphs reproject every time.
   The result is a strict-compatible certificate plus :world from actual helper
   work and :new-order. It does not publish or associate the final guest Env.
   Base assumptions retain their original admission; POLICY applies to additions.
   No serialized capability, lazy domain, subsumption or source replacement."
  [expected-basis context world values capability {:keys [fuel] :or {fuel 20000000} :as policy}]
  (let [{:keys [certificate sources environment helpers helper-code root quot? anchor] :as base}
        (locking issued (.get issued capability))]
    (require! base "An issued live checked-base capability is required" {})
    (require! (= expected-basis (:basis base))
              "Delta checking route rejects a different base provenance" {})
    (when (= :trusted-artifact expected-basis)
      (artifact/inspect-for-world world (get-in certificate [:kernel-provenance :artifact-admission]))
      (snapshot/validate-segments (:env certificate) (:java-guard-segments certificate)))
    (require! (and (vector? values) (integer? fuel) (<= 1 fuel Long/MAX_VALUE))
              "Explicit final refs and positive checker fuel required" {})
    (stage! :java-base)
    (current-java-base! certificate)
    (sources! world sources) (helper-code! context world helpers helper-code)
    (m/node world environment) (m/node world root)
    (let [[world actual-root actual-quot _] (read-environment context world environment helpers false)
          _ (stage! :base-association)
          current-anchor (get-in world [:kernel-environments (:id root)])]
      (require! (and (= root actual-root) (= quot? actual-quot)
                     (= anchor (select-keys current-anchor [:anchor :env :constant-map :quot-init? :kernel-provenance :java-guard-segments]))
                     (identical? (:env certificate) (:env current-anchor)))
                "Checked base association or quotient state changed" {})
      (sources! world sources) (helper-code! context world helpers helper-code)
      (when (= :trusted-artifact expected-basis)
        (artifact/inspect-for-world world (get-in certificate [:kernel-provenance :artifact-admission]))
        (snapshot/validate-segments (:env certificate) (:java-guard-segments certificate)))
      (stage! :java-base)
      (current-java-base! certificate)
      (stage! :delta-projection)
      (let [all (entries world values certificate) indexed (indexed! all)
            _ (stage! :inherited-shapes)
            _ (same-base! certificate indexed)
            base-names (set (keys (:constants certificate)))
            added (filterv #(not (contains? base-names (.name ^ConstantInfo (:constant %)))) all)
            _ (stage! :new-policy) _ (policy! world added policy)
            quotients (filter #(.isQuot ^ConstantInfo (:constant %)) added)
            _ (when (seq quotients)
                (require! (= #{"Quot" "Quot.mk" "Quot.lift" "Quot.ind"}
                             (set (map #(str (.name ^ConstantInfo (:constant %))) quotients)))
                          "New quotient bootstrap requires all four canonical primitives" {}))
            ;; Base dependencies are already available. Leaving them in the
            ;; old planner would turn name->group misses into nil blockers.
            _ (stage! :delta-plan)
            groups (mapv #(update % :dependencies set/difference base-names) (#'imported/groups added))
            new-names (map #(.name ^ConstantInfo (:constant %)) added)
            {:keys [members-by-key dependents degrees ready group-count]}
            (#'imported/checking-plan groups new-names)]
        (loop [queue ready cursor 0 degrees degrees ^Env checked (:env certificate) order []]
          (if (= cursor (count queue))
            (do
              (require! (= group-count cursor) "Unsupported recursive delta dependency group" {})
              (require! (= (set (keys indexed)) (set (map #(.name ^ConstantInfo %) (.allConstants checked))))
                        "Delta checker domain differs from complete final enumeration" {})
              (let [projected (into {} (map (fn [[name _]] [name (.lookup checked name)])) indexed)
                    new-projected (select-keys projected new-names)
                    segments (cond-> (vec (:java-guard-segments certificate))
                               (seq new-projected) (conj (snapshot/snapshot-segment new-projected)))]
                (cond-> {:world world :env checked :projection-sources sources
                         :constants (into {} (map (fn [[name entry]] [name (:guest entry)])) indexed)
                         :projected projected :new-order order
                         :kernel-provenance (:kernel-provenance certificate)
                         :java-guard-segments segments
                         :axioms (set/union (:axioms certificate)
                                           (set (map #(.name ^ConstantInfo (:constant %))
                                                     (filter #(.isAxiom ^ConstantInfo (:constant %)) added))))}
                  (= :strict-fresh expected-basis) (assoc :order (into (vec (:order certificate)) order)))))
            (let [key (nth queue cursor) members (get members-by-key key)
                  _ (stage! [:check key])
                  checked (case (first key)
                            :single (let [^ConstantInfo ci (first members)]
                                      (when (.isQuot ci) (#'imported/validate-quot-bootstrap checked))
                                      (TypeChecker/checkConstant checked ci (long fuel)))
                            :mutual (TypeChecker/checkMutualDefinitions checked members (long fuel))
                            :inductive (let [inds-by-name (into {} (map #(vector (.name ^ConstantInfo %) %) (filter #(.isInduct ^ConstantInfo %) members)))
                                             inds (mapv inds-by-name (second key)) first-ind ^ConstantInfo (first inds)]
                                         (env/check-inductive-bundle checked
                                           (env/mk-inductive-bundle (vec (.levelParams first-ind)) (.numParams first-ind) (.isUnsafe first-ind)
                                             inds (filterv #(.isCtor ^ConstantInfo %) members) (filterv #(.isRecursor ^ConstantInfo %) members)) fuel)))
                  [degrees queue] (reduce (fn [[degrees queue] dependent]
                                            (let [degree (dec (get degrees dependent))]
                                              [(assoc degrees dependent degree) (if (zero? degree) (conj queue dependent) queue)]))
                                          [degrees queue] (get dependents key))]
              (recur queue (inc cursor) degrees checked (conj order key)))))))))

(defn capture-base
  "Issue [latest-world opaque-live-capability] from actual checked association.
   Trusted strict certificate and current independently authorized helper context
   are required; no serialized authority. Guest map/source owners remain with
   the host. The helper enumeration must borrow the SAME CIs owned by that map,
   not temporary copies. Failures retain actual latest World and temporary owners."
  [context world environment helpers certificate]
  (operation world #(capture-base* context world environment helpers certificate)))

(defn verify-extension
  "CURRENT context, actual complete final CI refs, issued live base and new-policy
   produce a strict-compatible certificate plus actual :world/:new-order.
   Local inherited graphs reproject; only new groups are checked against the
   actual base Env. Final guest-map association/publication remains mandatory.
   Errors preserve latest World, stage and outstanding helper-owner evidence.
   The host serializes operations and prohibits concurrent Java CI mutation."
  [context world values capability policy]
  (operation world #(verify-extension* :strict-fresh context world values capability policy)))

(defn- capture-artifact-base* [context world environment helpers admission]
  (stage! :artifact-admission)
  (let [admitted (artifact/inspect-for-world world admission)
        sources (sources! world nil)
        roots (cond-> (mapv helpers [:root :constants :quot-init?])
                (:constant-map helpers) (conj (:constant-map helpers)))
        code (authority/capture context world roots)
        [world association] (kernel-host/resolve-association context world environment helpers)
        _ (publish! world)
        provenance (:kernel-provenance association)
        _ (require! (and association (= :trusted-artifact (:base-basis provenance))
                         (identical? admission (:artifact-admission provenance))
                         (= (:base-assumptions admitted) (:base-assumptions provenance)))
                    "Artifact capture requires the same issued artifact lineage" {})
        ^Env checked (:env association)
        segments (:java-guard-segments association)
        _ (require! (seq segments) "Artifact association lacks prior Java guards" {})
        ;; Validate the ORIGINAL witnesses before taking any new baseline.
        _ (snapshot/validate-segments checked segments)
        _ (stage! :artifact-current-enumeration)
        [world root quot? values] (read-environment context world environment helpers true)
        _ (require! (and (= root (:anchor association)) (= quot? (.isQuotEnabled checked)))
                    "Artifact current guest association or quotient state changed" {})
        seed (assoc admitted :env checked)
        indexed (indexed! (entries world values seed))
        projected (into {} (map (fn [^ConstantInfo ci] [(.name ci) ci])) (.allConstants checked))
        _ (require! (= (set (keys indexed)) (set (keys projected)))
                    "Current artifact descendant has incomplete guest CI domain" {})
        _ (doseq [[name {:keys [constant]}] indexed]
            (require! (= (imported/checking-shape constant)
                         (imported/checking-shape (get projected name)))
                      "Current artifact guest CI differs from its checked descendant" {:name name}))
        _ (doseq [[name guest] (:constants admitted)]
            (require! (= guest (get-in indexed [name :guest]))
                      "Missing or replaced inherited artifact reference" {:name name}))
        _ (artifact/inspect-for-world world admission)
        _ (snapshot/validate-segments checked segments)
        _ (sources! world sources)
        _ (authority/check context world roots code)
        _ (require! (= association (get-in world [:kernel-environments (:id root)]))
                    "Artifact association changed during current enumeration" {})
        projection {:env checked :projection-sources sources
                    :constants (into {} (map (fn [[name entry]] [name (:guest entry)])) indexed)
                    :projected projected :kernel-provenance provenance :java-guard-segments segments
                    :axioms (set (for [[name ^ConstantInfo ci] projected :when (.isAxiom ci)] name))}
        base (snapshot-projection projection)
        capability (CheckedBase.)]
    (locking issued
      (.put issued capability
            {:basis :trusted-artifact :certificate base :sources sources :environment environment
             :helpers helpers :helper-code (helper-code! context world helpers nil)
             :root root :quot? quot?
             :anchor (select-keys association [:anchor :env :constant-map :quot-init?
                                              :kernel-provenance :java-guard-segments])}))
    [world capability]))

(defn capture-artifact-base
  "Capture the CURRENT positive artifact descendant, authenticating the actual
   issued token and validating original/earlier Java guard segments before any
   replacement snapshot. The same token may cover successive checked additions;
   this does not require identity with its original artifact Java Env."
  [context world environment helpers admission]
  (operation world #(capture-artifact-base* context world environment helpers admission)))

(defn verify-artifact-extension
  "Check only additions against an issued live ARTIFACT-relative base. Preserve
   original artifact provenance/assumptions and prior witnesses, with :new-order
   only for this operation. No strict certificate or base checked order is made."
  [context world values capability policy]
  (operation world #(verify-extension* :trusted-artifact context world values capability policy)))
