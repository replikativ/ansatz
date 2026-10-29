(ns prototype.checked-delta
  "Live checked-base experiment. No serialized/trusted-artifact issuer.
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
            [prototype.eval-const :as eval]
            [ansatz.kernel.env :as env])
  (:import [ansatz.kernel Env ConstantInfo ConstantInfo$RecursorRule Expr TypeChecker]
           [java.util WeakHashMap IdentityHashMap]))

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
  (let [^Env checked (:env certificate) constants (:constants certificate) projected (:projected certificate)]
    (require! (and (instance? Env checked) (map? constants) (map? projected))
              "Actual strict verifier certificate required" {})
    (require! (.sameExternalView checked (Env.)) "Lazy/external checked bases are unsupported" {})
    (let [actual (into {} (map #(vector (.name ^ConstantInfo %) %) (.allConstants checked)))]
      (require! (= (set (keys constants)) (set (keys projected)) (set (keys actual)))
                "Checked base has incomplete Java ConstantInfo domain" {})
      (doseq [[name ^ConstantInfo ci] projected]
        (require! (and (instance? ConstantInfo ci) (= name (.name ci))
                       (identical? ci (get actual name)) (identical? ci (.lookup checked name)))
                  "Certificate projection differs from actual checked Env" {:name name})))
    certificate))

(defn- authority-code! [context world roots expected]
  (require! (and (fn? (:invoke context)) (map? (:trusted-functions context)))
            "Current authorized helper invoker and independent registry required" {})
  (require! (and (vector? roots) (every? vector? roots)) "Explicit guest helper targets required" {})
  (loop [pending roots functions {} bindings {}]
    (if (empty? pending)
      (let [actual {:functions functions :bindings bindings}]
        (when expected
          (require! (and (= (set (keys functions)) (set (keys (:functions expected))))
                         (= (set (keys bindings)) (set (keys (:bindings expected))))
                         (every? (fn [[name value]] (identical? value (get-in expected [:functions name]))) functions)
                         (every? (fn [[name value]] (identical? value (get-in expected [:bindings name]))) bindings))
                    "Checked base protected helper closure changed" {}))
        actual)
      (let [name (peek pending) pending (pop pending)]
        (if (contains? functions name) (recur pending functions bindings)
          (let [function (get-in world [:functions name])
                _ (require! (and (map? function) (identical? function (get (:trusted-functions context) name)))
                            "Checked base helper executable identity changed" {:name name})
                symbol (get-in function [:raw-extern :symbol])
                binding (when symbol (get (:bindings context) symbol))]
            (when symbol
              (require! (and binding (identical? binding (get (:trusted-bindings context) symbol)))
                        "Checked helper binding lacks independent identity authority" {:symbol symbol}))
            (recur (into pending (eval/executable-dependencies function))
                   (assoc functions name function) (cond-> bindings symbol (assoc symbol binding)))))))))

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
  ;; Typed bridge Expr fields are final, but CONST universe arguments may be
  ;; Java arrays. Keep only those mutable-container witnesses; share the DAG.
  (let [seen (IdentityHashMap.) arrays (IdentityHashMap.)
        roots (mapcat (fn [^ConstantInfo ci]
                        (concat [(.type ci) (.value ci)]
                                (when (.isRecursor ci)
                                  (map #(.rhs ^ConstantInfo$RecursorRule %) (.rules ci)))))
                      (vals (:projected certificate)))]
    (loop [pending (vec (remove nil? roots)) witnesses []]
      (if (empty? pending) witnesses
        (let [^Expr e (peek pending) pending (pop pending)]
          (if (.containsKey seen e) (recur pending witnesses)
            (do
              (.put seen e true)
              (let [levels (when (= Expr/CONST (.tag e)) (.o1 e))
                    array? (instance? (class (object-array 0)) levels)
                    fresh? (and array? (not (.containsKey arrays levels)))
                    _ (when fresh? (.put arrays levels true))
                    children (case (.tag e)
                               3 [(.o0 e) (.o1 e)]
                               (4 5) [(.o1 e) (.o2 e)]
                               6 [(.o1 e) (.o2 e) (.o3 e)]
                               (9 10) [(.o1 e)]
                               [])]
                (recur (into pending children)
                       (cond-> witnesses fresh? (conj [levels (mapv identity levels)])))))))))))

(defn- current-java-base! [certificate]
  ;; Env maps are persistent, but ConstantInfo exposes mutable Java fields.
  ;; Validate the objects actually used by the checker as well as guest data.
  ;; The owning host must still prohibit concurrent mutation during an operation.
  (eager-domain! certificate)
  (doseq [[name ^ConstantInfo ci] (:projected certificate)]
    (require! (= (get (:shapes certificate) name) (imported/checking-shape ci))
              "Inherited Java ConstantInfo checking shape changed" {:name name}))
  (doseq [[levels captured] (:expression-arrays certificate)]
    (require! (= captured (mapv identity levels))
              "Inherited Java expression universe array changed" {})))

(defn ^:no-doc snapshot-projection
  "Capture mutable Java containers in a complete eager projection.
   This is correspondence evidence only: it grants no checking or artifact
   admission authority. The owning host prevents concurrent mutation."
  [projection]
  (eager-domain! projection)
  (assoc projection
         :shapes (into {} (map (fn [[name ci]] [name (imported/checking-shape ci)]))
                       (:projected projection))
         :expression-arrays (expression-array-witnesses projection)))

(defn ^:no-doc validate-projection
  "Compare actual eager Java objects with captured container snapshots.
   Does not authenticate the projection or establish checking history."
  [snapshot]
  (current-java-base! snapshot)
  snapshot)

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
  (eager-domain! certificate)
  (require! (fn? (:invoke context)) "Authorized helper invoker required" {})
  (let [sources (sources! world nil) code (helper-code! context world helpers nil)
        [world root quot? values] (read-environment context world environment helpers true)
        _ (stage! :capture-association)
        anchor (get-in world [:kernel-environments (:id root)])
        checked (:env certificate)
        _ (require! (and (= root (:anchor anchor)) (identical? checked (:env anchor)))
                    "Existing positive checked association required" {})
        _ (require! (= quot? (.isQuotEnabled ^Env checked)) "Checked base quotient correspondence changed" {})
        _ (stage! :capture-projection)
        indexed (indexed! (entries world values certificate))
        base (snapshot-projection certificate)
        _ (require! (= (set (keys indexed)) (set (keys (:constants certificate))))
                    "Guest enumeration differs from complete checked base" {})
        _ (same-base! base indexed)
        _ (sources! world sources) _ (helper-code! context world helpers code)
        cap (CheckedBase.)]
    (locking issued
      (.put issued cap {:certificate base :sources sources :environment environment
                        :helpers helpers :helper-code code :root root :quot? quot?
                        :anchor (select-keys anchor [:anchor :env :constant-map :quot-init?])}))
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
  [context world values capability {:keys [fuel] :or {fuel 20000000} :as policy}]
  (let [{:keys [certificate sources environment helpers helper-code root quot? anchor] :as base}
        (locking issued (.get issued capability))]
    (require! base "An issued live checked-base capability is required" {})
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
                     (= anchor (select-keys current-anchor [:anchor :env :constant-map :quot-init?]))
                     (identical? (:env certificate) (:env current-anchor)))
                "Checked base association or quotient state changed" {})
      (sources! world sources) (helper-code! context world helpers helper-code)
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
              {:world world :env checked :projection-sources sources
               :constants (into {} (map (fn [[name entry]] [name (:guest entry)])) indexed)
               :projected (into {} (map (fn [[name _]] [name (.lookup checked name)])) indexed)
               :order (into (vec (:order certificate)) order) :new-order order
               :axioms (set/union (:axioms certificate)
                                 (set (map #(.name ^ConstantInfo (:constant %)) (filter #(.isAxiom ^ConstantInfo (:constant %)) added))))})
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
  (operation world #(verify-extension* context world values capability policy)))
