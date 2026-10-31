(ns allocation-heartbeat-cohort-v1
  "Explicit cohesive-cohort glue. Historical v1 helpers are untouched. Callbacks
   below are already authenticated host policy, never evidence booleans."
  (:require [clojure.data.json :as json] [clojure.java.io :as io]
            [java-ir-baseline :as j] [lean-compatibility-corpus :as corpus]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.authenticated-demand :as demand]
            [allocation-heartbeat-lab-v1 :as hb]
            [original-build-identity-provider-v1 :as build]
            [sequential-frontend-probe :as sp]
            [imported-frontend-setup-v4 :as imported-setup]
            [java-prelude-no-native-init :as native-init]
            [java-matched-prelude-module-v4 :as module]
            [java-prelude-finalizer-lineage-v1 :as lineage]
            [java-matched-artifact-base-v1 :as base]
            [artifact-declaration-driver-v4 :as checked-driver]
            [artifact-checked-declaration-adapter-v4 :as adapter]
            [generated-command-receipt-v1 :as command]
            [heartbeat-lab-options-proof :as options]
            [ansatz.export.storage :as storage]))
(defn- need [ok message] (when-not ok (throw (ex-info message {:scope :explicit-heartbeat-cohort-v1}))))
(def census {:nodes 97412 :positive 5659 :persistent 91753 :rc-sum 6140 :scalar-bytes 191928})
(defn open-companion! [basis dir expected census! journal]
  (let [manifest (json/read-str (slurp (str dir "artifact-manifest.json")))
        _ (doseq [file ["graph-capsule.json" "header-candidates.json"]]
            (assert (= (get-in manifest ["files" file "sha256"])
                       (corpus/sha256 (str dir file)))))
        headers (json/read-str (slurp (str dir "header-candidates.json")))
        capsule (json/read-str (slurp (str dir "graph-capsule.json")))
        _ (assert (= (get headers "source_index_sha256") (get-in capsule ["source" "code_index_sha256"])))
        base (j/prepare-host-program basis [] (get basis :early-host-specifications []))
        accepted-token (if-let [profile (:accepted-code-profile basis)]
                         (profile (get capsule "source")) (get capsule "source"))
        source ((:source-binding-factory basis) base accepted-token)
        by-sha (into {} (for [row (get headers "entries")]
                         [(get row "original_sha256")
                          (j/declaration-header source (get row "header_row") (get row "original_sha256"))]))
        raw-ctx (j/register-headers base (vec (vals by-sha)))
        configured (if-let [configure (:configure-import-context basis)]
                     (configure raw-ctx source by-sha) {:ctx raw-ctx :headers-by-sha {}})
        ctx (:ctx configured)
        all-headers (merge by-sha (:headers-by-sha configured))
        value (fn [x] (cond
                        (and (map? x) (= #{"ref"} (set (keys x)))) (j/graph-ref ctx (get x "ref"))
                        (and (map? x) (= #{"int"} (set (keys x)))) (j/graph-int ctx (java.math.BigInteger. ^String (get x "int")))
                        (map? x) (throw (ex-info "Unexpected capsule value" {:value x}))
                        :else x))
        nodes (mapv (fn [n]
                      (let [kind (keyword (get n "kind"))
                            descriptor {:kind kind :id (get n "id") :rc (get n "source_rc")
                                        :fields (mapv value (get n "fields"))}]
                        (j/graph-node ctx
                          (case kind
                            :ctor (assoc descriptor :tag (get n "tag")
                                         :scalars (mapv #(unchecked-byte (Integer/parseInt % 16))
                                                        (re-seq #".." (get n "scalar_hex"))))
                            :byte-array (do
                                          (assert (empty? (get n "fields")))
                                          (assoc (dissoc descriptor :fields) :bytes
                                            (mapv #(Integer/parseInt % 16)
                                                  (re-seq #".." (get n "scalar_hex")))))
                            :closure (assoc descriptor :target (or (by-sha (get n "header_sha256"))
                                                                   (throw (ex-info "Missing closure Header" {}))))
                            descriptor)))) (get capsule "nodes"))
        globals (mapv #(or (by-sha (get % "header_sha256")) (throw (ex-info "Missing global Header" {})))
                      (get capsule "globals"))
        import-profile (:graph-import-profile basis)
        _ (assert (contains? #{nil :persistent-ref-payload-mt} import-profile))
        state-token (if import-profile
                      {:source (get capsule "source") :target-import-profile "persistent-ref-payload-mt/1"}
                      (get capsule "source"))
        recipe-builder (if import-profile j/selected-owner-ref-payload-mt-graph j/selected-owner-graph)
        recipe (recipe-builder ctx source state-token nodes globals
                 (mapv #(value (get % "value")) (get capsule "globals"))
                 (mapv value (get capsule "owned_roots")))
        engine (j/machine ctx)
        _ (swap! journal assoc :stage :graph-install-pending :ctx ctx :engine engine :source source)
        start (System/nanoTime)
        roots (j/install-graph! ctx engine recipe)
        _ (swap! journal assoc :stage :graph-installed :roots roots)
        import-ms (/ (- (System/nanoTime) start) 1e6)
        _ (when-let [configure-engine (:configure-engine! configured)] (configure-engine ctx engine))
        census (census! ctx roots)
        _ (assert (= expected census))
        ]
    {:ctx ctx :engine engine :roots roots :source source :headers-by-sha all-headers
     :headers (count all-headers) :companion-headers (count by-sha) :globals (count globals) :census census
     :import-profile import-profile :install-ms import-ms :heap-max-mib (/ (.maxMemory (Runtime/getRuntime)) 1048576.0)
     :configuration configured
     :scope "Genuine selected companion import; no automatic fork or cleanup"}))


(defn- extra-service [session]
  (let [a (:additional-runtime-service session) b (get-in session [:driver :additional-runtime-service]) service (or a b)]
    (need (or (nil? a) (nil? b) (identical? a b)) "Parent/driver runtime service selection differs")
    (need (or (nil? service) (and (map? service) (= #{:handles? :serve!} (set (keys service)))
                                 (fn? (:handles? service)) (fn? (:serve! service)))) "Explicit trusted runtime service callbacks required")
    service))
(defn attach-runtime-service
  "Metadata-only opt-in; callbacks capture the NEW actual receipt, never an old
   engine/parent. Nil preserves old routing. Source/ABI/effect proof is in serve!."
  [parent service]
  (extra-service {:additional-runtime-service service})
  (assoc parent :additional-runtime-service service
                :driver (assoc (:driver parent) :additional-runtime-service service)))
(defn- reserved-runtime-symbol? [symbol]
  (contains? #{"lean_elab_add_decl" "lean_add_decl" "lean_run_mod_init_core"} symbol))
(defn runtime-service-step!
 ([session] (runtime-service-step! (or (:code-receipt session) (get-in session [:driver :code-receipt])) session))
 ([actual-code-receipt session]
  (let [d (:driver session) c @(:current-ctx d) e (:engine d) request (j/host-request c e)
        _ (need (and request (= "host-call" (j/phase c e))) "Actual runtime-service HostRequest required")
        symbol (j/request-value request "symbol") service (extra-service session)]
    (cond
      (hb/handles? symbol) (hb/serve-current! session)
      (build/handles? symbol) (build/serve! actual-code-receipt session)
      (and service (not (reserved-runtime-symbol? symbol)) ((:handles? service) symbol)) ((:serve! service) session)
      :else (throw (ex-info "Unsupported runtime service; request remains unclaimed" {:symbol symbol}))))))
(defn wrap-runtime-step [child admission]
  (let [original (:runtime-step! admission) service (extra-service child) expected (:driver child)
        step (fn [session]
               (let [d (:driver session) c @(:current-ctx d) e (:engine d)
                     request (when (= "host-call" (j/phase c e)) (j/host-request c e))
                     symbol (when request (j/request-value request "symbol"))]
                 (when (or service (build/handles? symbol))
                   (need (and (identical? e (:engine expected)) (identical? (:source d) (:source expected))
                              (identical? (:current-ctx d) (:current-ctx expected))
                              (identical? service (extra-service session))) "Foreign strict runtime service branch")
                   (need (not (contains? #{:failed :retired} @(get-in admission [:adapter :phase]))) "Terminal artifact adapter")
                   ((get-in admission [:authority :check-source!]) e (:source d)))
                 (cond
                   (and request (build/handles? symbol))
                   (do (swap! (:ticks admission) inc) (build/serve! (:code-receipt child) session))
                   (and service request (not (hb/handles? symbol)) (not (reserved-runtime-symbol? symbol)) ((:handles? service) symbol))
                   (do (swap! (:ticks admission) inc) ((:serve! service) session))
                   :else (original session))))]
    ;; HB keeps its existing strict checks/ticks; other unknowns still go to the
    ;; original checked driver, never a default/fake reply.
    (hb/wrap-step (:lab-heartbeat-provider child) (assoc admission :runtime-step! step))))
(defn host-step! [parent]
  (let [d (:driver parent) c @(:current-ctx d) e (:engine d) request (j/host-request c e)
        symbol (when request (j/request-value request "symbol"))]
    (source/guard-source! (:code-receipt parent) (:source d))
    (need (and request (= "host-call" (j/phase c e))) "Actual host boundary required")
    (cond
      (hb/handles? symbol) (hb/serve-current! parent)
      (= "lean_run_mod_init_core" symbol) (native-init/serve! (:native-init parent) d)
      :else (runtime-service-step! (:code-receipt parent) parent))))
(defn drive! [parent budget]
  (source/guard-source! (:code-receipt parent) (get-in parent [:driver :source]))
  (loop [left budget]
    (let [d (:driver parent) c @(:current-ctx d) e (:engine d) phase (j/phase c e)]
      (cond
        (zero? left) {:phase phase :status :budget}
        (= "code-call" phase) (do (demand/service-code! d) (recur (dec left)))
        (= "running" phase) (do (j/advance! c e 1000) (recur (dec left)))
        (= "host-call" phase) (do (host-step! parent) (recur (dec left)))
        :else {:phase phase :status :boundary}))))
(defn guest-call! [parent label args]
  (let [d (:driver parent) e (:engine d) header (demand/ensure-header! d (sp/typed-name label))
        c (j/register-headers @(:current-ctx d) [header])]
    (need (= "idle" (j/phase c e)) "Call requires idle")
    (j/install-program! c e) (reset! (:current-ctx d) c)
    (j/start! c e label args)
    (let [boundary (drive! parent 20000)]
      (need (= "complete" (:phase boundary)) "Cohort call paused; preserve parent owners")
      (j/take-result! @(:current-ctx d) e))))
(defn array-values! [parent xs]
  (reduce (fn [a x] (guest-call! parent "Array.push" [0 a x]))
          (guest-call! parent "Array.mkEmpty" [0 0]) xs))
(defn open-parent!
  "CONFIGURED-BASIS is the existing finalizer-runtime-basis-v1 result. Callbacks:
   :open-driver! [live] -> actual authenticated-demand driver;
   :configure! [driver] -> {:driver same-driver :native-init actual-cap}; performs
   all existing zero-work policies plus Substring8/Meta2/audit21. :census! is the
   existing bounded census reader. Optional :configure-child! [child journal] runs
   guest default-stream construction ONLY after each pristine fork; never on seed.
   Optional :journal receives actual runtime roots through installation failures.
   No ambient user Vars or extra source mint."
  [configured-basis receipt directory {:keys [open-driver! configure! census!] :as policy}]
  (need (every? fn? [open-driver! configure! census!]) "Explicit actual host policy functions required")
  (let [journal (or (:journal policy) (atom {}))]
    (try
     (let [early (get configured-basis :early-host-specifications [])
        descriptor (hb/bootstrap-specification! receipt)
        _ (need (and (vector? early) (not-any? #(= hb/set-symbol (:symbol %)) early)) "Do not duplicate early setter policy")
        basis (assoc configured-basis :early-host-specifications (conj early descriptor))
        live (open-companion! basis directory census census! journal)
        driver (assoc (open-driver! live) :code-receipt receipt) e (:engine live)
        _ (swap! journal assoc :driver driver :live live :stage :policy-configuration)
        _ (need (and (identical? e (:engine driver)) (identical? (:source live) (:source driver))) "Driver changed actual live engine/source")
        configured (configure! driver) d (:driver configured)
        _ (need (and (identical? e (:engine d)) (identical? (:source driver) (:source d))
                     (identical? (:current-ctx driver) (:current-ctx d))) "Configuration changed driver identity")
        _ (need (and (:native-init configured) (= "idle" (j/phase @(:current-ctx d) e))
                     (zero? (j/instructions @(:current-ctx d) e))) "Policies must finish without guest instructions")
        parent {:driver d :live live :code-receipt receipt :native-init (:native-init configured)
                :configuration (:configuration live) :bootstrap-lineage nil
                :state :runtime-ready-no-logical-base :startup-status (atom {:state :pending}) :census! census!
                :configure-child! (:configure-child! policy) :layout-directory (:layout-directory policy)}
        provider (hb/install! parent)]
    (let [attached (attach-runtime-service (hb/attach parent provider) (:additional-runtime-service policy))]
      (swap! journal assoc :parent attached :stage :runtime-ready)
      attached))
     (catch Throwable error
       (throw (ex-info "Cohort parent preparation failed; preserve actual runtime journal" {:journal @journal} error))))))
(defn fork-seed! [parent]
  (let [d (:driver parent) c @(:current-ctx d) e (:engine d)]
    (need (and (= :runtime-ready-no-logical-base (:state parent)) (nil? (:bootstrap-lineage parent))
               (= :pending (:state @(:startup-status parent))) (= "idle" (j/phase c e)) (zero? (j/instructions c e)))
          "Only pristine unassociated pending-startup seed can fork here")
    (let [packet (hb/fork! (:lab-heartbeat-provider parent) (:roots d)) child-driver (:driver packet)
          _ (need (= census ((:census! parent) c (:roots packet))) "Fork census differs")
          child (assoc parent :driver child-driver :live (assoc (:live parent) :ctx c :engine (:engine packet) :roots (:roots packet))
                       :startup-status (atom {:state :pending}))]
      (attach-runtime-service (hb/attach child (:provider packet)) (extra-service parent)))))

(defn startup! [parent]
 (let [startup (:startup-status parent)]
  (assert startup)
  (swap! startup
         (fn [s] (assert (= :pending (:state s))) {:state :running}))
  (let [d (:driver parent) e (:engine d)
        before (j/instructions @(:current-ctx d) e)
        value (guest-call! parent "JavaModuleImport.finalize._boxed_const_1" [])
        ctx @(:current-ctx d)]
    (reset! startup {:state :value-result-owned :value value
                    :body-instructions (- (j/instructions ctx e) before)})
    (assert (= 0 value))
    (j/start-release! ctx e value 1)
    (assert (= "complete" (:phase (drive! parent 20000))))
    (j/take-result! @(:current-ctx d) e)
    (reset! startup
            {:state :ready :label "JavaModuleImport.finalize._boxed_const_1"
             :actual-body-executed true :result-released true}))))
(defn assemble! [parent aggregate input]
  (let [d (:driver parent) fs (fn [x] (.get ^java.lang.reflect.Field (:fields @(:current-ctx d)) x))
        parts (vec (fs aggregate))
        module (first (:modules input))
        _ (assert (= 1 (count (:modules input))))
        _ (assert (= ["str" ["str" ["anonymous"] "Init"] "Prelude"] (:module module)))
        wrap (fn [part]
               (let [i (:rootIndex part) a (:artifact part)]
                 (assert (<= 0 i 4))
                 (assert (<= 0 (:mappedBytes a) Long/MAX_VALUE))
                 ;; Module roots are persistent. Their additional owning occurrence
                 ;; is a normal retain (no-op at RC0), never a fabricated credit.
                 (j/retain! @(:current-ctx d) (:engine d) (nth parts i))
                 (guest-call! parent "JavaModuleImport.mkVirtualPart"
                   [(nth parts i) (:filePath a) (long (:mappedBytes a))])))
        wrapped-parts (array-values! parent (mapv wrap (:parts module)))
        wrapped-ir (array-values! parent (mapv wrap (:irParts module)))
        flag (fn [x] (assert (instance? Boolean x)) (if x 1 0))
        effective (:effectiveImport module)
        _ (assert (= "all" (:irPhases module)))
        imported (guest-call! parent "JavaModuleImport.mkImportedModule._boxed"
                   ["Init.Prelude" (flag (:importAll effective)) (flag (:isExported effective))
                    (flag (:isMeta effective)) 2 (flag (:hasData module)) (flag (:needsIRTrans module))
                    wrapped-parts wrapped-ir])
        state (guest-call! parent "JavaModuleImport.assembleImportState._boxed"
                [(array-values! parent [imported])])
        requested (first (:requestedImports input))
        _ (assert (= 1 (count (:requestedImports input))))
        _ (assert (= (:module module) (:module requested)))
        request (guest-call! parent "JavaModuleImport.mkRequestedImport._boxed"
                  ["Init.Prelude" (flag (:importAll requested)) (flag (:isExported requested)) (flag (:isMeta requested))])
        requests (array-values! parent [request])]
    {:state state :imports requests :actual-source-constructors true
     :requested-import requested :effective-import effective}))

(defn begin-finalizer! [parent module-lease assembled]
  (let [d (:driver parent) e (:engine d) m (module/inspect! module-lease)
        input (get-in m [:census :manifest :input])
        requested (first (:requestedImports input)) effective (:effectiveImport (first (:modules input)))
        state (:state assembled) imports (:imports assembled)
        header (demand/ensure-header! d (sp/typed-name "JavaModuleImport.finalize._boxed"))]
    (assert (identical? e (:engine m)))
    (lineage/begin! parent
      {:finalizer-header header :state-slot (object-array [state :owned]) :imports-slot (object-array [imports :owned])
       :quantum 1000 :max-transitions 20000 :max-instructions 20000000
       :extra-code-overlays (get parent :extra-code-overlays [])
       :deadline-nanos (+ (System/nanoTime) 60000000000) :expected-constants 2314
       :check-leases! #(module/inspect! module-lease)
       :validate-inputs! (fn [engine source actual-state actual-imports]
                          (let [current (module/inspect! module-lease)]
                            (assert (and (identical? e engine) (identical? engine (:engine current))))
                            (assert (and (identical? source (:source d)) (identical? source (:code-source current))))
                            (assert (identical? actual-state state)) (assert (identical? actual-imports imports))
                            (assert (= requested (:requested-import assembled)))
                            (assert (= effective (:effective-import assembled)))))
       :service-code! (fn [driver request]
                        (assert (identical? request (j/code-request @(:current-ctx driver) (:engine driver))))
                        (demand/service-code! driver))
       :service-host! (fn [p request]
                        (let [d (:driver p)]
                          (need (identical? request (j/host-request @(:current-ctx d) (:engine d))) "Foreign finalizer host request")
                          (host-step! p)))})))

(defn setup!
 ([driver real-env text filename]
  (setup! driver real-env text filename ["Hosted" "SequentialProbe"]))
 ([driver real-env text filename module-segments]
  (assert (and (vector? module-segments) (<= 1 (count module-segments) 256)
               (every? #(and (string? %) (seq %) (not (re-find #"[.\\/\u0000]" %))) module-segments)))
  (let [s {:driver driver :runtime-step! runtime-service-step! :owners (atom {}) :observations (atom []) :calls (atom []) :in-flight (atom nil)
           :deadline-nanos (+ (System/nanoTime) 60000000000)
           :limits {:instructions 3000000 :code-requests 3000 :turns 50000 :commands 3}
           :used (atom {:instructions 0 :code-requests 0 :turns 0 :commands 0})}]
    (try
      ;; FIRST check: no guest call, retain or reflective allocation before this.
      (sp/preflight-real-env! s real-env)
      (assert (= "idle" (j/phase (sp/ctx s) (sp/engine s))))
      (assert (:task-runtime (sp/ctx s)) "Require explicit active synchronous runtime")
      (let [size (sp/call! s "String.utf8ByteSize" [text])
            input (sp/hold! s :input (sp/call! s "Lean.Parser.mkInputContext._redArg" [text filename 1 size]))]
        (sp/ctor! s input 0 4)
        (sp/hold! s :header-result (sp/call! s "Lean.Parser.parseHeader" [(sp/facade-owner! s :input) 0]))
        (let [payload (aget ^objects (sp/ctor! s (sp/owned s :header-result) 0 1) 0)
              pair (sp/ctor! s payload 0 2) rest (sp/ctor! s (aget ^objects pair 1) 0 2)]
          (sp/retain-as! s :header (aget ^objects pair 0))
          (sp/retain-as! s :parser-state (aget ^objects rest 0))
          (sp/retain-as! s :header-messages (aget ^objects rest 1)))
        (sp/drop! s :header-result)
        (sp/retain-as! s :header-messages-observation (sp/owned s :header-messages))
        (assert (not (sp/error-log? s :header-messages)) "Header diagnostics reported errors")
        (assert (not (sp/bool! (sp/call! s "Lean.Elab.HeaderSyntax.isModule" [(sp/facade-owner! s :header)]))) "Module file outside fixed probe")
        (sp/hold! s :prelude-stx (sp/call! s "Lean.Syntax.getArg" [(sp/facade-owner! s :header) 1]))
        (assert (not (sp/bool! (sp/call! s "Lean.Syntax.isNone" [(sp/take-owner! s :prelude-stx)]))) "Actual prelude required")
        (assert (not (sp/bool! (sp/call! s "Lean.Elab.HeaderSyntax.isModule" [(sp/facade-owner! s :header)])))
                "This fixed first profile requires Lean legacy/private mode")
        (sp/hold! s :imports (sp/call! s "Lean.Elab.HeaderSyntax.imports" [(sp/facade-owner! s :header) 1]))
        (imported-setup/validate-prelude-imports! s (sp/owned s :imports))
        (sp/drop! s :imports)
        (sp/drop! s :header)
        (sp/hold! s :module-name (sp/call! s "Lean.Name.mkStr1" [(first module-segments)]))
        (doseq [segment (rest module-segments)]
          (sp/hold! s :module-segment (sp/call! s "Lean.Name.mkStr1" [segment]))
          (sp/hold! s :module-name (sp/call! s "Lean.Name.appendCore"
                                [(sp/take-owner! s :module-name) (sp/take-owner! s :module-segment)])))
        (let [module-name (sp/take-owner! s :module-name)]
          (j/retain! (sp/ctx s) (sp/engine s) real-env)
          (sp/hold! s :environment (sp/call! s "Lean.Environment.setMainModule" [real-env module-name])))
        (sp/hold! s :options (sp/call! s "Lean.Options.empty" []))
        (doseq [[prefix leaf] (concat [["Elab" "async"] ["debug" "skipKernelTC"]]
                                      (get (sp/ctx s) :lab-false-bool-options []))]
          (let [name (sp/call! s "Lean.Name.mkStr2" [prefix leaf])]
            (sp/hold! s :options (sp/call! s "Lean.Options.setBool" [(sp/take-owner! s :options) name 0]))))
        ;; Strict native-kernel prototype: disable the TWO original native
        ;; resource limits through real guest options. VM/projection/checker
        ;; host budgets remain separately enforced and are not native counters.
        (doseq [option ["maxHeartbeats" "maxRecDepth"]]
          (let [name (sp/call! s "Lean.Name.mkStr1" [option])
                nat-value-instance (sp/call! s "Lean.KVMap.instValueNat" [])]
            (sp/hold! s :options (sp/call! s "Lean.Options.set" [0 nat-value-instance (sp/take-owner! s :options) name 0]))))
        (sp/hold! s :command-state (sp/call! s "Lean.Elab.Command.mkState"
                                  [(sp/take-owner! s :environment) (sp/take-owner! s :header-messages) (sp/take-owner! s :options)]))
        (let [ps (sp/owned s :parser-state) f (sp/ctor! s ps 0 1)]
          (assert (= 2 (alength ^bytes (sp/scalars s ps))))
          (sp/retain-as! s :command-pos (aget ^objects f 0)))
        (sp/hold! s :commands (sp/call! s "Array.emptyWithCapacity" [0 0]))
        (sp/assemble-state! s)
        (sp/hold! s :state-ref (sp/call! s "ST.Prim.mkRef" [0 0 (sp/take-owner! s :frontend-state) 0]))
        {:status :prepared :session s :initial-observation (sp/snapshot! s 0)
         :adapter-allocations 1 :checked-declaration-established false})
      (catch Throwable error
        (sp/failure s error))))))

(defn- prepare-source-child-with!
  "Journal child custody before activation. Store descriptor is explicit borrowed
   host input, not inferred by this unit; existing Module/Run/Base issuers validate.
   STORE contains :path and actual :manifest. All phases keep one branch Provider."
  [open-checked-driver journal parent prepared-module text filename module-segments store]
  (let [layout-directory (or (:layout-directory store) (:layout-directory parent))
        _ (need (and (string? layout-directory) (seq layout-directory)) "Explicit authenticated layout artifact directory required")
        forked (fork-seed! parent)
        child0 (update forked :driver assoc :code-receipt (:code-receipt forked))
        _ (swap! journal assoc :child child0)
        d (:driver child0) imported (module/install! prepared-module d)
        _ (swap! journal assoc :module imported)
        _ (startup! child0)
        ;; Genuine local-value startup is complete before source default-stream
        ;; construction; construction still precedes logical import/frontend.
        configured (if-let [configure-child! (:configure-child! parent)]
                     (do (need (fn? configure-child!) "Explicit child configuration function required")
                         (configure-child! child0 journal)) child0)
        _ (need (and (identical? (get-in child0 [:driver :engine]) (get-in configured [:driver :engine]))
                     (identical? (get-in child0 [:driver :source]) (get-in configured [:driver :source]))
                     (identical? (get-in child0 [:driver :current-ctx]) (get-in configured [:driver :current-ctx]))
                     (identical? (:lab-heartbeat-provider child0) (:lab-heartbeat-provider configured))
                     (identical? (extra-service child0) (extra-service configured))) "Child configuration changed actual branch/source/provider/service")
        child configured _ (swap! journal assoc :child child :child-configured true)
        m (module/inspect! imported) assembled (assemble! child (:aggregate m) (get-in m [:census :manifest :input]))
        _ (swap! journal assoc :assembled assembled)
        run (begin-finalizer! child imported assembled)
        _ (swap! journal assoc :run run)
        final (lineage/poll! run 20000)
        _ (need (= :ready (:status final)) "Finalizer paused/failed; preserve journal")
        lease (atom true) backing (assoc (storage/open-store (:path store)) :lease! #(need @lease "Store lease revoked"))
        _ (swap! journal assoc :store backing :store-lease lease)
        matched (base/open-base! imported run backing (:manifest store))
        _ (swap! journal assoc :base matched)
        setup (setup! d (:environment (lineage/inspect! run)) text filename module-segments)
        _ (swap! journal assoc :setup setup)
        _ (need (= :prepared (:status setup)) "Frontend setup paused/failed; preserve journal")
        admission (open-checked-driver child matched run
                    {:layout-directory layout-directory :heartbeat-step! hb/serve-current!})
        frontend (assoc (:session setup) :runtime-step! (wrap-runtime-step child admission))]
    (swap! journal assoc :admission admission :frontend frontend)
    :prepared))
(defn prepare-source-child!
  "Legacy finite checked child, sixteen-admission driver captured once."
  [journal parent prepared-module text filename module-segments store]
  (prepare-source-child-with! checked-driver/open-driver journal parent prepared-module
                             text filename module-segments store))
(defn prepare-general-source-child!
  "General-command child,512-admission driver captured before runtime wrapping.
   This is a fresh child factory, not a session replacement on an existing driver.
   Startup, module/base/Run custody, heartbeat and extra-service routing match
   prepare-source-child!; parser/command limits remain separately explicit."
  [journal parent prepared-module text filename module-segments store]
  (prepare-source-child-with! checked-driver/open-general-driver journal parent prepared-module
                             text filename module-segments store))
(defn retire-engine!
  "Only healthy explicit root retirement; Provider stays live through every
   callback-capable release/disposal, then revokes after actual disposal and close."
  [parent extra-owners]
  (let [d (:driver parent) e (:engine d)]
    (need (and (nil? (:bootstrap-lineage parent)) (= "idle" (j/phase @(:current-ctx d) e))) "Healthy unassociated idle retirement required")
    (doseq [v (concat extra-owners (:roots d))]
      (need (some? v) "Actual owner occurrence required")
      (j/start-release! @(:current-ctx d) e v 1)
      (need (= "complete" (:phase (drive! parent 20000))) "Release paused; preserve actual owner journal")
      (need (= 0 (j/take-result! @(:current-ctx d) e)) "Release did not return Unit"))
    (j/start-dispose! @(:current-ctx d) e)
    (need (= "complete" (:phase (drive! parent 20000))) "Dispose paused; preserve actual owner journal")
    (need (= 0 (j/take-result! @(:current-ctx d) e)) "Dispose did not return Unit")
    (j/close! @(:current-ctx d) e)
    (hb/revoke! (:lab-heartbeat-provider parent))
    {:status :disposed-and-closed :extra-owner-occurrences (count extra-owners) :runtime-root-occurrences (count (:roots d))}))
(defn retire-source-child! [journal]
  (let [{:keys [child frontend admission run module store store-lease command-run]} @journal
        frontend (options/rebase-idle-deadline frontend)]
    (when command-run
      (command/rebase-idle-deadline! command-run 60000)
      (command/retire! command-run))
    ;; Frontend releases still have live strict authority and SAME pair wrapper.
    (sp/release-session! frontend)
    (let [packet (vec (concat (adapter/take-retirement-owners! (:adapter admission))
                             (map second (lineage/take-retirement-owners! run))
                             [(module/take-retirement-owner! module)]))
          _ (swap! journal assoc :retirement-packet packet)
          result (retire-engine! child packet)]
      (reset! store-lease false) (storage/close-store store)
      (reset! journal {:retirement result}) result)))
