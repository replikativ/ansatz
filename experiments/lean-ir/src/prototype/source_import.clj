(ns prototype.source-import
  "Authenticated owned classic source import: standalone or over the exact
   native Init prefix, with no source initializer actions. Registry refs are owned by the immutable world, never
   captured by callbacks or disguised as native compacted-memory provenance."
  (:require [prototype.machine :as m] [prototype.kernel-bridge :as bridge]
            [prototype.source-module :as source] [prototype.module-import :as module-import]
            [prototype.kernel-host :as kernel-host]
            [prototype.import-capabilities :as native-caps] [prototype.runtime-string :as string]
            [prototype.native-scalar :as native] [prototype.module-init-capabilities :as module-init]
            [prototype.module-store :as store])
  (:import [ansatz.kernel Env]))

(defn- helper [part] ["str" ["str" ["anonymous"] "SourceModuleImport"] part])
(def helpers {:part (helper "mkOwnedPart") :assemble (helper "assembleClassic")
              :finalize (helper "finalizeClassic") :header (helper "finalizerHeader")})
(def hybrid-assemble-helper (helper "appendClassicOverInit"))
(def init-module ["str" ["anonymous"] "Init"])
(def init-request {:module init-module :importAll false :isExported true :isMeta false})
;; Pinned HeaderSyntax.imports prepends BOTH ordinary and meta Init.
(def init-requests [init-request (assoc init-request :isMeta true)])
(def ^:private ops {:ref? m/ref? :node m/node})
(defn- fail [message data] (throw (ex-info message data)))
(defn- ctor [world value tag fields scalar]
  (let [node (when (m/ref? value) (m/node world value))]
    (when-not (and (= tag (:tag node)) (bridge/constructor-layout? node fields scalar))
      (fail "Invalid owned source object layout" {:value value})) node))
(defn- array [world value]
  (let [node (when (m/ref? value) (m/node world value))]
    (when-not (= :array (:kind node)) (fail "Invalid owned source array" {})) (:fields node)))

(defn- validate-unit
  ([world compilation] (validate-unit world compilation []))
  ([world compilation expected-imports]
  (let [handle (:handle compilation) module (:module-name handle) digest (:unit-digest handle)
        original (:world compilation) environment (:environment compilation)
        unit (get-in world [:eval-const-authorizations :units digest])
        previous (get-in original [:eval-const-authorizations :units digest])]
    (module-import/module-string module)
    (when-not (and (true? (:success compilation)) (true? (get-in compilation [:envelope :success]))
                   (= "complete" (get-in compilation [:envelope :stage]))
                   (= module (get-in compilation [:envelope :mainModule]))
                   (string? digest) (re-matches #"[0-9a-f]{64}" digest)
                   unit (identical? unit previous) (vector? (:actions unit)) (empty? (:actions unit))
                   (= module (get-in unit [:manifest :initializationPlan :module]))
                   (= (mapv (fn [i] {:module (:module i) :meta (:isMeta i)}) expected-imports)
                      (get-in unit [:manifest :initializationPlan :imports]))
                   (= [] (get-in unit [:manifest :initializationPlan :actions]))
                   (false? (get-in compilation [:envelope :moduleSystem]))
                   (= expected-imports (get-in compilation [:envelope :requestedImports]))
                   (m/ref? environment)
                   (not (m/native-reference? world environment))
                   (= (dissoc (m/node original environment) :rc) (dissoc (m/node world environment) :rc)))
      (fail "Source registration requires the same authenticated successful compilation world" {:module module}))
    (doseq [name (:declarations unit)]
      (let [f (get-in world [:functions name]) old (get-in original [:functions name])
            admitted (get-in world [:eval-const-authorizations :functions name])]
        (when-not (and f (identical? f old) (identical? f admitted))
          (fail "Source compilation executable identity changed" {:name name}))))
    {:module module :digest digest :unit unit :environment environment :original original})))

(defn- protected-compilation-root [world invoke original environment root]
  (let [old (get-in original [:kernel-environments (:id root)])
        current (get-in world [:kernel-environments (:id root)])]
    (if (and old current (= root (:anchor old) (:anchor current)) (identical? (:env old) (:env current))) world
      (let [[world constants] (invoke world (:constant-map module-import/helpers) [environment])
            [world flag] (invoke world (:quot-init? module-import/helpers) [environment])
            flag (native/nat-value ops world flag)
            _ (when-not (contains? #{0 1} flag) (fail "Invalid source compilation quotient flag" {:checkpoint world}))
            matched
            (some (fn [entry]
                    (let [current (get-in world [:kernel-environments (:id (:anchor entry))])]
                      (when (and (= constants (:constant-map entry) (:constant-map current))
                                 (= (= 1 flag) (:quot-init? entry) (:quot-init? current))
                                 (= (:anchor entry) (:anchor current))
                                 (identical? (:env entry) (:env current))) entry)))
                  (vals (:kernel-environments original)))]
        (when-not (and matched (m/ref? root) (m/ref? constants))
          (fail "Source checked environment lacks the original protected association" {:checkpoint world :root root}))
        (when (and current (not (identical? (:env current) (:env matched))))
          (fail "Source checked environment has a conflicting association" {:checkpoint world :root root}))
        ;; Exact protected constant-map identity plus quotient state authorizes
        ;; this header-only root, as in kernel-host. Keep its OWN root anchor.
        (-> world (m/release constants 1)
            (cond-> (nil? current) (m/retain root 1))
            (assoc-in [:kernel-environments (:id root)]
              {:anchor root :env (:env matched) :constant-map constants :quot-init? (= 1 flag)}))))))

(defn- register-profile [world invoke compilation module-name expected-imports profile]
  (let [{:keys [module digest environment original]} (validate-unit world compilation expected-imports)
        _ (when-not (= (module-import/module-string module) (str (bridge/project-name world module-name)))
            (fail "Source registration module Name mismatch" {}))
        [world root] (invoke world (:root module-import/helpers) [environment])
        world (protected-compilation-root world invoke original environment root)
        world (m/release world root 1)]
    (when (contains? (:source-modules world) module)
      (fail "Source module is already published in this world" {:module module}))
    (let [exported (source/export-classic world invoke environment module-name)]
      (when-not (= :ok (:status exported))
        (fail "Source module export failed" {:checkpoint (:world exported) :io-result (:io-result exported)}))
      (let [world (:world exported) data (:module-data exported) metadata (:metadata exported)
            node (ctor world data 0 5 1)
            imports (array world (first (:fields node)))
            key (str "ansatz-source:" digest)
            _ (when-not (and (= module (:module metadata)) (= (count expected-imports) (count imports))
                             (= expected-imports (:imports metadata))
                             (not (m/native-reference? world data)) (nil? (:native-source-id node)))
                (fail "Source import profile requires exact owned classic dependencies" {:checkpoint world :module-data data}))
            _ (when (contains? (:source-regions world) key) (fail "Conflicting source region key" {:checkpoint world}))
            entry {:module module :unit-digest digest :unit (:unit (validate-unit world compilation expected-imports))
                   :profile profile
                   :data data :environment environment :metadata metadata :key key}
            world (-> world (m/retain environment 1)
                      (assoc-in [:source-modules module] entry)
                      (assoc-in [:source-regions key] {:module module :data data :anchors {}}))]
        {:world world :entry entry}))))

(defn register-compiled
  "Publish only the original dependency-free, initializer-free classic profile.
   Exports inside the compatible compilation world; returned entry refs borrow
   registry owners. This does not admit an ordinary implicit-Init file."
  [world invoke compilation module-name]
  (register-profile world invoke compilation module-name [] :standalone))

(defn register-compiled-over-init
  "Publish the explicit ordinary classic profile: exact implicit Init imports,
   no local initializer actions, same admitted compilation and executable world.
   Import reconstruction and its checked receipt are separate operations."
  [world invoke compilation module-name]
  (when (= init-module (get-in compilation [:handle :module-name]))
    (fail "Source module cannot replace the native Init prefix" {}))
  (register-profile world invoke compilation module-name init-requests :over-init))

(defn- entry! [world module]
  (let [entry (get-in world [:source-modules module]) unit (:unit entry)]
    (when-not (and entry (identical? unit (get-in world [:eval-const-authorizations :units (:unit-digest entry)])))
      (fail "Source module is not registered in this authenticated world" {:module module}))
    (ctor world (:data entry) 0 5 1)
    (doseq [name (:declarations unit)]
      (when-not (identical? (get-in world [:functions name]) (get-in world [:eval-const-authorizations :functions name]))
        (fail "Published source executable identity changed" {:name name})))
    entry))

(defn unregister
  "Drop only registry-owned roots when no logical region anchors remain.
   Persistent RC0 graphs remain persistent; this is not a reclaim guarantee.
   Other snapshots, caller owners, environments and code are unaffected."
  [world module]
  (let [entry (entry! world module)]
    (when (seq (get-in world [:source-regions (:key entry) :anchors]))
      (fail "Source publication still has live region anchors" {:module module}))
    (-> world (update :source-modules dissoc module) (update :source-regions dissoc (:key entry))
        (m/release (:data entry) 1) (m/release (:environment entry) 1))))

(defn- region! [world region & {:keys [unanchored?]}]
  (let [node (when (m/ref? region) (m/node world region))
        _ (when-not (and (= :ctor (:kind node)) (= 0 (:tag node))
                         (= {:objects 2 :usize 3 :ssize 1} (:layout node))
                         (= 2 (count (:fields node))))
            (fail "Invalid owned source region layout" {}))
        [path root] (:fields node) key (string/string-value ops world path)
        registration (get-in world [:source-regions key]) entry (entry! world (:module registration))]
    (when-not (and registration (= key (:key entry)) (= root (:data entry) (:data registration))
                   (every? zero? (map #(m/read-scalar-node node %)
                                    [{:index 2 :offset 0 :type "usize" :region :usize}
                                     {:index 3 :offset 0 :type "usize" :region :usize}
                                     {:index 4 :offset 0 :type "usize" :region :usize}
                                     {:index 5 :offset 0 :type "uint8" :region :scalar}]))
                   (or unanchored? (= region (get-in registration [:anchors (:id region)]))))
      (fail "Unregistered, freed or native source region" {:key key}))
    {:key key :data root :node node}))

(defn- native-init-closure! [loaded]
  (let [world (:world loaded) input (get-in loaded [:manifest :input])
        requests (:requestedImports input) modules (:modules loaded)
        expected init-requests
        _ (when-not (and (= "private" (:globalLevel input)) (true? (:transitiveClosure input))
                         (= expected requests)
                         (= init-module (:module (last modules))))
            (fail "Hybrid source import requires the explicit native Init closure profile" {}))
        ;; Validate all transported part provenance/dependency-chain capabilities.
        _ (native-caps/make-bindings loaded)
        by-name (into {} (map (fn [mod] [(module-import/module-string (:module mod)) mod])) modules)
        _ (when-not (= (count by-name) (count modules)) (fail "Duplicate native prefix module" {}))
        dependencies
        (loop [remaining modules seen #{} result {}]
          (if-let [mod (first remaining)]
            (let [name (module-import/module-string (:module mod))
                  effective (:effectiveImport mod) parts (:parts mod)
                  _ (when-not (and (= (:module mod) (:module effective))
                                   (true? (:importAll effective)) (false? (:isExported effective))
                                   (boolean? (:isMeta effective)) (true? (:hasData mod))
                                   (= "all" (:irPhases mod)) (boolean? (:needsIRTrans mod)))
                      (fail "Native Init prefix must preserve private effective imports" {:module (:module mod)}))
                  first-node (ctor world (:value (first parts)) 0 5 1)
                  module? (m/read-scalar-node first-node {:index 5 :offset 0 :type "uint8" :region :scalar})
                  _ (when-not (or (and (= 0 module?) (= 1 (count parts)))
                                  (and (= 1 module?) (= 3 (count parts))))
                      (fail "Native Init prefix has incomplete selected data parts" {:module (:module mod)}))
                  selected (:value (if (= 1 module?) (last parts) (first parts)))
                  node (ctor world selected 0 5 1)
                  deps (mapv (fn [request]
                               (let [request (ctor world request 0 1 3)]
                                 (str (bridge/project-name world (first (:fields request))))))
                             (array world (first (:fields node))))]
              (when-not (every? seen deps)
                (fail "Native Init prefix is not a complete dependency-first closure" {:module (:module mod)}))
              (recur (next remaining) (conj seen name) (assoc result name deps)))
            result))
        reachable (loop [pending ["Init"] seen #{}]
                    (if-let [name (peek pending)]
                      (if (contains? seen name) (recur (pop pending) seen)
                        (recur (into (pop pending) (get dependencies name)) (conj seen name))) seen))]
    (when-not (= reachable (set (keys by-name)))
      (fail "Native Init prefix contains unrelated modules" {}))
    loaded))

(defn- local-prefix-nodes [world state]
  ;; Bound provenance to the local ImportState scaffold. Native ModuleData DAGs
  ;; are immutable Store-owned leaves and must never be copied into this witness.
  (loop [pending [state] nodes {}]
    (if-let [ref (peek pending)]
      (let [pending (pop pending)]
        (if (or (not (m/ref? ref)) (contains? nodes (:id ref)))
          (recur pending nodes)
          (let [node (m/node world ref)]
            (if (m/native-reference? world ref) (recur pending nodes)
              (recur (into pending (filter m/ref? (:fields node)))
                     (assoc nodes (:id ref) (dissoc node :rc)))))))
      nodes)))

(defn prepare-init-prefix
  "Reassemble a pinned native Init ImportState from an existing verified Store,
   retaining one registry owner. No source reopening, decoding of the full DAG,
   native export or finalization. CHECKED is the actual protected Init import
   result (:environment/:certificate), in LOADED's compatible descendant world.
   The producer requests [Init, meta Init], matching pinned implicit imports.
   Its effective records are preserved; the final header adds A in order.
   Returns an opaque, borrowed :prefix receipt plus the updated :world."
  ([loaded invoke checked] (prepare-init-prefix loaded invoke checked {}))
  ([loaded invoke checked options]
   (let [world (:world loaded) source (:source loaded)
         _ (when-not (and (= 1 (count (:native-imports world)))
                          (identical? source (first (:native-imports world))))
             (fail "Hybrid Init prefix requires one exact attached native source" {}))
         ;; Re-derive descriptors from THIS world's exact attached source. Caller
         ;; maps/Refs alone cannot authenticate a replacement native closure.
         actual (store/describe-attached world source)
         _ (when-not (and (= (:modules loaded) (:modules actual)) (= (:manifest loaded) (:manifest actual)))
             (fail "Native prefix descriptors differ from the attached verified source" {}))
         _ (native-init-closure! actual)
         certificate (:certificate checked)
         _ (when-not (and (= :ok (:status checked)) (instance? Env (:env certificate))
                          (= 1 (count (:projection-sources certificate)))
                          (identical? source (first (:projection-sources certificate))))
             (fail "Native Init prefix requires its complete immutable checked certificate" {}))
         [world root] (invoke world (:root module-import/helpers) [(:environment checked)])
         anchored (get-in world [:kernel-environments (:id root)])
         _ (when-not (and (= root (:anchor anchored)) (identical? (:env certificate) (:env anchored)))
             (fail "Native Init certificate has no protected association in this world" {:checkpoint world}))
         world (m/release world root 1)
         assembled (module-import/assemble (assoc actual :world world) invoke
                                           (assoc options :module-system? false))
         world (m/release (:world assembled) (:imports assembled) 1)
         state (:state assembled)
         prefix {:state state :local-nodes (local-prefix-nodes world state)
                 :source source :checked-anchor root :checked-env (:env certificate)
                 :constants (:constants certificate) :modules (:modules assembled)
                 :producer-imports (:requested assembled)}
         _ (when (get-in world [:source-import-prefixes (:id state)])
             (fail "Native prefix state is already registered" {:checkpoint world}))]
     {:world (assoc-in world [:source-import-prefixes (:id state)] prefix) :prefix prefix})))

(defn- prefix! [world prefix]
  (let [registered (get-in world [:source-import-prefixes (:id (:state prefix))])
        anchored (get-in world [:kernel-environments (:id (:checked-anchor prefix))])
        source (:source prefix)]
    (when-not (and (identical? prefix registered)
                   (= (:checked-anchor prefix) (:anchor anchored))
                   (identical? (:checked-env prefix) (:env anchored))
                   (= 1 (count (:native-imports world)))
                   (identical? source (first (:native-imports world)))
                   (false? @(:closed source)))
      (fail "Native Init prefix is not authenticated in this world" {}))
    (let [start (:base source) end (+ start (:size source))]
      (when (some #(and (integer? %) (<= start %) (< % end)) (keys (:heap world)))
        (fail "Native Init prefix immutable source range is shadowed" {})))
    (doseq [[id expected] (:local-nodes prefix)]
      (when-not (= expected (dissoc (m/node world (m/->Ref id)) :rc))
        (fail "Native Init prefix local scaffold changed" {:id id})))
    prefix))

(defn release-init-prefix
  "Release this world's registry owner. Other snapshots and assembled import
   states keep their own ownership; the shared native Store stays caller-owned."
  [world prefix]
  (prefix! world prefix)
  (-> world (update :source-import-prefixes dissoc (:id (:state prefix)))
      (m/release (:state prefix) 1)))

(defn assemble
  "Create actual guest ImportedModule/ImportState. Returned :state/:imports are
   owned; the world registry owns the extra region anchor. Name is borrowed."
  [world invoke module module-name]
  (let [entry (entry! world module)
        _ (when-not (= :standalone (:profile entry))
            (fail "Standalone assembly requires a dependency-free source publication" {}))
        _ (when-not (= (module-import/module-string module) (str (bridge/project-name world module-name)))
            (fail "Source assembly module Name mismatch" {}))
        [world assembly] (invoke (m/retain world (:data entry) 1) (:assemble helpers)
                                 [(:data entry) module-name (:key entry)])
        [state imports region] (:fields (ctor world assembly 0 3 0))
        world (-> world (m/retain state 1) (m/retain imports 1) (m/retain region 1) (m/release assembly 1))
        _ (region! world region :unanchored? true)
        world (assoc-in world [:source-regions (:key entry) :anchors (:id region)] region)]
    {:world world :state state :imports imports :module module
     :requested-imports [{:module module :importAll false :isExported true :isMeta false}]}))

(defn assemble-over-init
  "Borrow authenticated prefix and source publication; append A with the real
   pinned guest helper. REQUESTS must be B's actual parsed [Init,meta Init,A] header.
   Prefix owner is retained, so independent compatible branches may reuse it."
  [world invoke prefix module module-name requests]
  (let [prefix (prefix! world prefix) entry (entry! world module)
        expected (conj init-requests {:module module :importAll false :isExported true :isMeta false})
        _ (when-not (and (= :over-init (:profile entry)) (= expected requests)
                         (= init-requests (get-in entry [:metadata :imports]))
                         (= (module-import/module-string module) (str (bridge/project-name world module-name)))
                         (not-any? #(= module (:module %)) (:modules prefix)))
            (fail "Hybrid assembly requires exact ordinary [Init,meta Init,A] source imports" {}))
        [world result] (invoke (-> world (m/retain (:state prefix) 1) (m/retain (:data entry) 1))
                               hybrid-assemble-helper [(:state prefix) (:data entry) module-name (:key entry) m/erased])
        node (when (m/ref? result) (m/node world result))
        _ (when-not (and (contains? #{0 1} (:tag node)) (bridge/constructor-layout? node 1 0))
            (fail "Malformed hybrid assembly IO.Result" {:checkpoint world :io-result result}))]
    (if (= 1 (:tag node))
      {:status :io-error :world world :io-result result}
      (let [assembly (first (:fields node))
            [state imports region] (:fields (ctor world assembly 0 3 0))
            world (-> world (m/retain state 1) (m/retain imports 1) (m/retain region 1) (m/release result 1))
            _ (region! world region :unanchored? true)
            world (assoc-in world [:source-regions (:key entry) :anchors (:id region)] region)]
        {:status :ok :world world :state state :imports imports :module module
         :prefix prefix :requested-imports requests}))))

(defn make-bindings
  "No guest Ref is captured. Reads/frees consult only this world's explicit
   source registry. These bindings do not serve native transported regions.
   Free drops a logical region root owner, never invalidates separately owned
   constants or unmaps memory. Persistent regions explicitly cannot be freed."
  []
  (merge (module-init/make-bindings)
  {"lean_runtime_mark_persistent"
   {:signature (get native-caps/signatures "lean_runtime_mark_persistent")
    :handler (fn [_ world [_ value _]] [(m/mark-persistent world value) value])}
   "lean_compacted_region_read"
   {:signature (get native-caps/signatures "lean_compacted_region_read")
    :handler
    (fn [{:keys [invoke]} world [_ path dependencies _]]
      (let [key (string/string-value ops world path) registered (get-in world [:source-regions key])
            entry (entry! world (:module registered))]
        (when-not (and registered (= key (:key entry)) (empty? (array world dependencies)))
          (fail "Unregistered source read or unsupported source dependencies" {}))
        (let [[world pair] (invoke (m/retain world (:data entry) 1) (:part helpers) [(:data entry) path])
              [data region] (:fields (ctor world pair 0 2 0))
              _ (when-not (= data (:data entry)) (fail "Source read constructor changed data" {:checkpoint world}))
              _ (region! world region :unanchored? true)
              world (-> world (m/retain region 1)
                        (assoc-in [:source-regions key :anchors (:id region)] region))]
          (m/allocate world :ctor 0 [pair]))))}
   "lean_compacted_region_free"
   {:signature (get native-caps/signatures "lean_compacted_region_free")
    :handler
    (fn [_ world [region _]]
      (let [{:keys [key data node]} (region! world region)]
        (when (zero? (:rc node)) (fail "Persistent source region cannot be reclaimed" {}))
        (let [world (-> world
                        (update-in [:source-regions key :anchors] dissoc (:id region))
                        (m/replace-node region (assoc node :fields (assoc (:fields node) 1 0)))
                        (m/release data 1) (m/release region 2))]
          (m/allocate world :ctor 0 [0]))))}}))

(defn make-hybrid-bindings
  "Compose source region operations with ALREADY authenticated native bindings.
   Native reads retain their exact part-dependency checks; source reads/free use
   this world's registry. The native module initializer availability capability
   is preserved by identity, including its completed dependency/phase guards.
   ansatz-source: is reserved for source regions, never native artifact paths."
  [native-bindings]
  (doseq [[symbol signature] (assoc native-caps/signatures
                                   "lean_run_mod_init_core" module-init/signature)]
    (let [binding (get native-bindings symbol)]
      (when-not (and (= signature (:signature binding)) (fn? (:handler binding)))
        (fail "Hybrid capabilities require authenticated native region and initializer bindings"
              {:symbol symbol}))))
  (let [source-bindings (make-bindings)
        source-key? (fn [world path]
                      (or (contains? (:source-regions world) path)
                          (.startsWith ^String path "ansatz-source:")))
        route (fn [symbol path-index]
                {:signature (get native-caps/signatures symbol)
                 :handler
                 (fn [context world args]
                   (let [value (nth args path-index)
                         path (if (= symbol "lean_compacted_region_free")
                                (first (:fields (m/node world value))) value)
                         path (string/string-value ops world path)
                         binding (get (if (source-key? world path) source-bindings native-bindings) symbol)]
                     ((:handler binding) context world args)))})]
    (assoc native-bindings
      "lean_compacted_region_read" (route "lean_compacted_region_read" 1)
      "lean_compacted_region_free" (route "lean_compacted_region_free" 0))))

(defn- record-source-receipt* [finished invoke module options base-constants]
  (if-not (= :ok (:status finished)) finished
    (let [world (:world finished) entry (entry! world module)
          [names constants] (subvec (:fields (ctor world (:data entry) 0 5 1)) 1 3)
          names (mapv #(bridge/project-name world %) (array world names))
          values (array world constants)
          _ (when-not (= (count names) (count (set names)) (count values))
              (fail "Published source has duplicate or mismatched constant names" {:checkpoint world}))
          expected (zipmap names values)
          _ (when (some #(contains? base-constants %) names)
              (fail "Hybrid source import cannot subsume native Init constants" {:checkpoint world}))
          all-expected (merge base-constants expected)
          certificate (:certificate finished)
          _ (when-not (= all-expected (:constants certificate))
              (fail "Finalized source CI references differ from the published import graph"
                    {:checkpoint world :environment (:environment finished)}))
          [world root] (invoke world (:root (merge module-import/helpers (:helpers options))) [(:environment finished)])
          anchor (get-in world [:kernel-environments (:id root)])
          _ (when-not (and (= root (:anchor anchor)) (identical? (:env certificate) (:env anchor)))
              (fail "Finalized source kernel association differs from the checked certificate" {:checkpoint world}))
          ;; The full certificate checked Init+A; source authorization needs only
          ;; A's exact subset, inherited by subsequent protected environments.
          receipt {:anchor root :checked-env (:env certificate) :constants expected
                   :projected (select-keys (:projected certificate) names) :unit-digest (:unit-digest entry)}
          world (-> world (m/release root 1)
                    (assoc-in [:source-modules module :imports (:id root)] receipt))]
      (assoc finished :world world :source-import-receipt receipt))))

(defn- record-source-receipt [finished invoke module options base-constants]
  (try
    (record-source-receipt* finished invoke module options base-constants)
    (catch Throwable cause
      ;; Receipt validation follows successful whole-map association. Keep its
      ;; owned Environment/certificate with THEIR world, even if a later helper
      ;; produced a newer failure checkpoint. No guest effects are replayed.
      (throw (ex-info (or (.getMessage cause) "Source import receipt failed")
                     (merge {:checkpoint (:world finished)} (ex-data cause)
                            {:source-finalization-result finished}) cause)))))

(defn finalize
  "Consume assembled state/imports through genuine finalization, then strict CI
   checking and exact finalizer-header quotient-state projection. Options borrow
   the caller's Options ref. Success owns the returned Environment."
  [assembly invoke options-ref options]
  (let [{:keys [world state imports requested-imports]} assembly
        _ (when-not (= :standalone (:profile (entry! world (:module assembly))))
            (fail "Standalone finalization requires a dependency-free source publication" {}))
        [world result] (invoke world (:finalize helpers) [state imports options-ref m/erased])
        finished (module-import/finish-finalization world result invoke
                   (assoc options :finalizer-attestation
                     {:requested-imports requested-imports :header-helper (:header helpers)}))]
    (record-source-receipt finished invoke (:module assembly) options nil)))

(defn- hybrid-finalization-input! [assembly world]
  (let [{:keys [requested-imports module prefix]} assembly
        prefix (prefix! world prefix)
        original (entry! (:world assembly) module) current (entry! world module)
        _ (when-not (and (= :ok (:status assembly)) (= :over-init (:profile (entry! world module)))
                         (identical? (:unit original) (:unit current)) (= (:data original) (:data current))
                         (= requested-imports
                            (conj init-requests {:module module :importAll false :isExported true :isMeta false})))
            (fail "Invalid authenticated hybrid assembly" {}))]
    ;; Extension callbacks may link additional functions. Existing reviewed
    ;; finalization/root/header implementations may not be replaced meanwhile.
    (doseq [target (concat [(:finalize helpers) (:header helpers)] (vals module-import/helpers))]
      (when-not (identical? (get-in assembly [:world :functions target]) (get-in world [:functions target]))
        (fail "Hybrid finalization helper identity changed" {:target target})))
    prefix))

(defn finish-over-init
  "Complete strict checking/receipt association of an ALREADY completed genuine
   finalizer IO.Result in its actual WORLD. Never calls or replays the finalizer.
   ASSEMBLY supplies the same authenticated prefix/source lineage; WORLD owns
   RESULT. On errors the finalizer entry/checking checkpoints remain diagnostic
   alternatives, not permission to rerun effects. Source receipts cover A only;
   the whole Init+A map is checked, with exact refs and no native subsumption."
  [assembly world result invoke options]
  (let [prefix (hybrid-finalization-input! assembly world)
        finished (module-import/finish-finalization world result invoke
                   (assoc options :finalizer-attestation
                     {:requested-imports (:requested-imports assembly) :header-helper (:header helpers)}))]
    (record-source-receipt finished invoke (:module assembly) options (:constants prefix))))

(defn finalize-over-init
  "Consume hybrid assembly through genuine guest finalization, then finish its
   strict whole-map association. For a long run, retain the raw finalizer result
   separately and call finish-over-init at that completion boundary instead."
  [assembly invoke options-ref options]
  (let [{:keys [world state imports]} assembly
        _ (hybrid-finalization-input! assembly world)
        [world result] (invoke world (:finalize helpers) [state imports options-ref m/erased])]
    (finish-over-init assembly world result invoke options)))

(defn authorize-imported-row
  "Narrow evalConst capability. ROW must carry the actual interpreter witness's
   :sourceModule. UNIT is the original admitted immutable unit receipt. The
   caller still checks exact selected IR/ABI and executable closure identities.
   This additionally resolves the target's ACTUAL checked root and proves its
   checked constants inherit the exact CI objects installed by source finalization.
   No world-independent guest references are captured."
  [world context environment row local unit]
  (let [module (:sourceModule row) entry (get-in world [:source-modules module])
        digest (get-in world [:eval-const-authorizations :unit-digests (:name row)])]
    (if-not (and entry (identical? unit (:unit entry)) (= digest (:unit-digest entry))
                 (identical? local (get-in world [:eval-const-authorizations :declarations (:name row)]))
                 (false? (:sourceLocal row))) [world false]
      (let [checker (:check-trusted-functions! context)
            _ (when-not (fn? checker) (fail "Source import authorization requires trusted helper closure checking" {}))
            _ (checker world (mapv module-import/helpers [:root :constant-map :quot-init?]))
            [world current] (kernel-host/inherit-checked-association context world environment module-import/helpers)
            ^Env current current
            accepted
            (and current
                 (some (fn [receipt]
                         (let [anchored (get-in world [:kernel-environments (:id (:anchor receipt))])]
                           (and (= (:unit-digest entry) (:unit-digest receipt))
                                (= (:anchor receipt) (:anchor anchored))
                                (identical? (:checked-env receipt) (:env anchored))
                                (every? (fn [[name ci]] (identical? ci (.lookup current name)))
                                        (:projected receipt)))))
                       (vals (:imports entry))))]
        [world (boolean accepted)]))))
