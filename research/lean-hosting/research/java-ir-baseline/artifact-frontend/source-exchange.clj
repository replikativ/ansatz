(ns java-source-module-exchange-v1
  "Actual source-produced ModuleData on one engine. No serialized Environment,
   native region transport, unchecked Java Env factory or active-association fork."
  (:require [clojure.data.json :as json]
            [clojure.string :as str]
            [prototype.kernel-bridge :as bridge]
            [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.authenticated-demand :as demand]
            [ansatz.research.ir.kernel-projection :as projection]
            [prototype.imported-kernel :as imported]
            [prototype.kernel-projection-snapshot :as snapshot]
            [java-matched-prelude-module-v4 :as module]
            [java-matched-artifact-base-v1 :as prelude]
            [java-prelude-finalizer-lineage-v1 :as lineage]
            [general-command-receipt-v1 :as command]
            [artifact-checked-declaration-adapter-v4 :as adapter]
            [generated-command-receipt-v1 :as finite]
            [general-generated-batch-v1 :as generated]
            [allocation-heartbeat-cohort-v1 :as cohort])
  (:import [java.util WeakHashMap] [ansatz.kernel ConstantInfo Name]))

(deftype SourceRuntime [])
(deftype Operation [])
(deftype SourceModule [])
(deftype SourceClosure [])
(deftype FinalizedSourceRun [])
(defonce ^:private runtimes (WeakHashMap.))
(defonce ^:private operations (WeakHashMap.))
(defonce ^:private modules (WeakHashMap.))
(def helper-source-sha "54b0a48c3ca041a8ebeddcdee7fa1f23f425bd07b470df6537c03d49e74ee88d")
(def helper-module ["str" ["anonymous"] "SourceModuleExchange"])
(def prelude-name ["str" ["str" ["anonymous"] "Init"] "Prelude"])
(def graph-limits [17 16 64 16 32768 256 4096 4194304 4096 65536])
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :source-module-exchange-v1}))))
(defn- issued [registry token]
  (locking registry (or (.get ^WeakHashMap registry token) (throw (ex-info "Actual source exchange capability required" {})))))
(defn- publish! [registry token value] (locking registry (.put ^WeakHashMap registry token value)) token)
(defn- field [x k] (#'lineage/field x k))
(defn- context [s] @(:current-ctx (:driver s)))
(defn- root-value [slot] (aget ^objects slot 0))
(defn- root-state [slot] (aget ^objects slot 1))
(defn- ordinary [s value tag count scalar-sizes]
  (#'lineage/guard-node (:engine s) "constructorNode" value)
  (let [ctx (context s) fs ^objects (.get ^java.lang.reflect.Field (:fields ctx) value)
        bytes ^bytes (.get ^java.lang.reflect.Field (:scalars ctx) value)]
    (need (and (nil? (field value "closure")) (= tag (.getInt ^java.lang.reflect.Field (:tag ctx) value))
               (= count (alength fs)) (contains? scalar-sizes (alength bytes))) "Source module constructor layout differs")
    {:fields fs :bytes bytes}))
(defn- array-values [s value limit]
  (let [node (#'lineage/guard-node (:engine s) "array" value)
        n (.arraySize node) fs ^objects (.get ^java.lang.reflect.Field (:fields (context s)) node)]
    (need (and (<= 0 n limit) (<= n (alength fs))) "Source module logical Array size exceeds bounds")
    (mapv #(aget fs %) (range n))))
(defn- scoped [s f]
  (let [scope (projection/open-projector (context s) (:engine s)
                {:max-nodes 100000 :deadline-nanos (+ (System/nanoTime) 10000000000)})]
    (try (f scope) (finally ((:close! scope))))))
(defn- typed-name [scope value]
  (bridge/project-name-bounded (:world scope) value {:max-nodes 256 :max-chars 65536} (:carrier-ops scope)))
(defn- wire-name [^Name name]
  (loop [n name parts []]
    (need (< (count parts) 256) "Source module Name spine exceeds bound")
    (case (.tag n)
      0 (reduce (fn [p [tag leaf]] [tag p leaf]) ["anonymous"] (rseq parts))
      1 (recur (.prefix n) (conj parts ["str" (.str n)]))
      2 (recur (.prefix n) (conj parts ["num" (Long/toUnsignedString (.num n))])))))
(defn- runtime! [holder]
  (let [s @holder]
    (need (= :open (:status s)) "Source exchange runtime is closed or failed")
    (need (identical? (:thread s) (Thread/currentThread)) "Source exchange is thread confined")
    (let [ctx (context s) d (:driver s) e (:engine s)
          m (module/inspect! (:module-lease s)) r (lineage/inspect! (:prelude-run s))]
      (need (and (identical? e (:engine d)) (identical? (:source s) (:source d))
                 (identical? (:program ctx) (field e "program"))
                 (identical? e (:engine m)) (identical? e (:engine r))
                 (identical? (:source s) (:code-source m)) (identical? (:source s) (:source r)))
            "Source exchange module/original Prelude Run/driver identity differs")
      (source/guard-source! (:code-receipt s) (:source s))
      (doseq [key ["closed" "disposed" "untrackedFailure" "advancing"]]
        (need (false? (field e key)) "Source exchange engine lifecycle changed"))) s))
(defn open-runtime!
  "Borrow actual same-engine ModuleLease and ORIGINAL fixed Prelude Run. Fresh
   strict Prelude Base is supplied separately for each reconstruction because
   retiring an adapter revokes its old Base. No arbitrary graph is admitted."
  [parent module-lease original-prelude-run]
  (let [driver (:driver parent) receipt (:code-receipt parent)
        profile (source/code-profile receipt) entries (get profile "overlays")
        _ (need (and (= 4 (count entries)) (= helper-module (get (last entries) "module"))
                     (= helper-source-sha (get (last entries) "source_sha256"))
                     (= [] (get-in (last entries) ["initializationPlan" "actions"])))
                "Authenticated fourth source exchange overlay required")
        extra (mapv #(select-keys % ["module" "source_sha256" "local_ir_sha256" "export_receipt_sha256"
                                    "producer_sha256" "base_index_sha256"]) (drop 2 entries))
        holder (atom {:status :open :thread (Thread/currentThread) :parent parent :driver driver
                      :engine (:engine driver) :source (:source driver) :code-receipt receipt
                      :module-lease module-lease :prelude-run original-prelude-run :extra-code-overlays extra :active nil :keepers []})]
    (#'lineage/check-code-profile! profile extra)
    (runtime! holder)
    (publish! runtimes (SourceRuntime.) holder)))
(defn- watch-owners! [rh cell]
  ;; A keeper retains ONLY shared owner slots/status, never a holder, token,
  ;; parent-module capability, adapter or callback. Full module holders here
  ;; would create transitive weak-key cycles through their parent capabilities.
  (let [keeper {:owners (atom (:owners @cell)) :status (atom (:status @cell)) :output (object-array 1)}]
    (add-watch cell (Object.) (fn [_ _ _ now]
                              (reset! (:owners keeper) (:owners now))
                              (reset! (:status keeper) (:status now))))
    (swap! rh update :keepers (fnil conj []) keeper)
    keeper))
(defn- operation! [runtime]
  (let [rh (issued runtimes runtime) r (runtime! rh) marker (Object.) token (Operation.)
        _ (need (and (nil? (:active r)) (= "idle" (j/phase (context r) (:engine r)))) "A source exchange operation is active or engine is not idle")
        check! (fn []
                 (let [now @rh]
                   (need (= :open (:status now)) "Source exchange runtime failed")
                   (module/inspect! (:module-lease now)) (lineage/inspect! (:prelude-run now))))
        cell (atom {:status :active :thread (:thread r) :driver (:driver r) :engine (:engine r) :source (:source r)
                    :code-receipt (:code-receipt r) :parent (:parent r) :runtime-holder rh :marker marker
                    :extra-code-overlays (:extra-code-overlays r)
                    :startup-status (get-in r [:parent :startup-status])
                    :startup-snapshot (select-keys @(get-in r [:parent :startup-status]) [:state :label :actual-body-executed :result-released])
                    :startup-header (first (get-in r [:parent :configuration :local-action-headers]))
                    :owners {} :history [] :call nil :stage :source-exchange
                    :options {:check-leases! check! :deadline-nanos (+ (System/nanoTime) 120000000000)
                              :max-instructions 50000000 :max-transitions 100000}})]
    ;; The runtime records only a private marker, never Operation/Module tokens.
    (let [keeper (watch-owners! rh cell)]
      (swap! cell assoc :keeper keeper)
      (swap! rh assoc :active marker) (publish! operations token cell) [token cell])))
(defn- fail! [cell cause]
  (swap! cell assoc :status :failed :failure {:class (.getName (class cause))
      :message (subs (or (.getMessage cause) "Source exchange failed") 0 (min 800 (count (or (.getMessage cause) "Source exchange failed"))))})
  (swap! (:runtime-holder @cell) assoc :status :failed :active nil))
(defn- finish! [cell]
  (swap! (:runtime-holder @cell) assoc :active nil)
  (swap! cell assoc :status :sealed))
(defn- call! [cell key label values]
  (let [s (#'lineage/live! cell) d (:driver s)
        h (demand/ensure-header! d (reduce (fn [p x] ["str" p x]) ["anonymous"] (str/split label #"\.")))
        c (j/register-headers (context s) [h])
        _ (j/install-program! c (:engine s)) _ (reset! (:current-ctx d) c)
        arguments (mapv (fn [i v] (#'lineage/retain! cell [key :arg i] v)) (range) values)]
    (#'lineage/start-call! cell key h label values arguments)
    (loop [left 100000]
      (need (pos? left) "Source exchange call transition bound")
      (let [now (#'lineage/current-root! cell) c (context now) e (:engine now) phase (j/phase c e)]
        (case phase
          "running" (do (j/advance! c e 1000) (recur (dec left)))
          "code-call" (do (demand/service-code! d) (recur (dec left)))
          "host-call" (do (cohort/host-step! (:parent now)) (recur (dec left)))
          "complete" (let [slot (#'lineage/new-owner! cell key nil :take-pending)
                           answer (j/take-result! c e)]
                       (aset ^objects slot 0 answer) (aset ^objects slot 1 :owned)
                       (swap! cell assoc :call nil) answer)
          (throw (ex-info "Source exchange stopped at unsupported runtime boundary" {:phase phase})))))))
(defn- retain! [cell key value] (#'lineage/retain! cell key value) value)
(defn- release! [cell key]
  (let [slot (get-in @cell [:owners key]) s (#'lineage/live! cell)
        unit (#'lineage/new-owner! cell [key :release-result] nil :take-pending)]
    (need (= :owned (root-state slot)) "Source exchange release occurrence is not owned")
    (swap! cell assoc :release {:key key :owner-slot slot :result-slot unit :stage :before-start})
    (aset ^objects slot 1 :release-pending)
    (j/start-release! (context s) (:engine s) (root-value slot) 1)
    (aset ^objects slot 1 :transferred)
    (loop [left 100000]
      (need (pos? left) "Source exchange release transition bound")
      (let [s (#'lineage/live! cell) c (context s) e (:engine s)]
        (case (j/phase c e)
          "running" (do (j/advance! c e 1000) (recur (dec left)))
          "code-call" (do (demand/service-code! (:driver s)) (recur (dec left)))
          "host-call" (do (cohort/host-step! (:parent s)) (recur (dec left)))
          "complete" (let [answer (j/take-result! c e)]
                       (aset ^objects unit 0 answer) (aset ^objects unit 1 :owned)
                       (need (and (instance? Long answer) (= 0 answer)) "Release did not return actual Unit")
                       (aset ^objects unit 1 :immediate-consumed)
                       (aset ^objects slot 0 nil)
                       (swap! cell dissoc :release))
          (throw (ex-info "Source exchange release paused; preserve owner packet" {})))))))
(defn- clean! [cell keep]
  (doseq [[key slot] (:owners @cell) :when (and (= :owned (root-state slot)) (not (contains? keep key)))]
    (release! cell key)))
(defn owner-packet [operation]
  (select-keys @(issued operations operation) [:status :stage :owners :call :release :failure]))

(declare check-module-data!)
(defn- module! [token full?]
  (let [cell (issued modules token) s @cell]
    (need (= :sealed (:status s)) "Source module is revoked or failed")
    (let [r (runtime! (:runtime-holder s))]
    (doseq [key [:module-data :module-name]]
      (need (= :owned (root-state (get-in s [:owners key]))) "Source module occurrence was retired"))
    (doseq [parent (:parents s)] (module! parent full?))
    (ordinary r (root-value (get-in s [:owners :module-data])) 0 5 #{1 8})
    (need (and (:payload-snapshot s)
               (every? true? (map identical? (:roots (:payload-snapshot s))
                                 [(root-value (get-in s [:owners :module-data]))
                                  (root-value (get-in s [:owners :module-name]))])))
          "Source module payload witness/owned roots differ")
    ((requiring-resolve 'ansatz.research.ir.source-data-snapshot/validate!) (:payload-snapshot s))
    (when full?
      (doseq [segment (:snapshot-segments s)] (snapshot/validate-segment-values segment))
      (check-module-data! r s))
    s)))
(defn- read-only! [r f]
  (let [before (#'finite/hook-stamp (:engine r))]
    (try (f)
      (finally
        (let [after (#'finite/hook-stamp (:engine r))]
          (need (and (= (:counts before) (:counts after)) (= (:flags before) (:flags after))
                     (every? true? (map identical? (:identities before) (:identities after))))
                "Source exchange metadata borrow advanced guest state"))))))
(defn with-module! [token f]
  (let [s (module! token true) r (runtime! (:runtime-holder s))]
    (read-only! r #(try (f (:view s)) (finally (module! token true))))))
(defn- imports! [r scope value]
  (mapv (fn [input]
          (let [{:keys [fields bytes]} (ordinary r input 0 1 #{3 8})
                flags (mapv #(Byte/toUnsignedInt (aget ^bytes bytes %)) (range 3))]
            (need (= [0 1 0] flags) "Source modules require ordinary classic requested imports")
            {:module (wire-name (typed-name scope (aget ^objects fields 0)))
             :importAll false :isExported true :isMeta false}))
        (array-values r value 17)))
(defn- data-index! [r scope data version]
  (let [{:keys [fields bytes]} (ordinary r data 0 5 #{1 8})
        _ (need (zero? (Byte/toUnsignedInt (aget ^bytes bytes 0))) "Module-system source data is not supported")
        names (mapv #(typed-name scope %) (array-values r (aget ^objects fields 1) 4096))
        infos (array-values r (aget ^objects fields 2) 4096)
        _ (need (= (count names) (count infos) (count (:payloads version))) "Exported source CI domain count differs from checked locals")
        ^ansatz.kernel.Env env (:env version)
        index (reduce (fn [out [name info]]
                        (let [{actual-name :name kind :kind} (imported/project-constant-name-kind
                                                             (:world scope) info {:max-nodes 256 :max-chars 65536} (:carrier-ops scope))
                              wrapper ((:node (:carrier-ops scope)) (:world scope) info)
                              payload (first (:fields wrapper)) expected (get (:payloads version) name)
                              ^ConstantInfo ci (.lookupLocal env name)]
                          (need (and (not (contains? out name)) (= name actual-name) ci expected
                                     (= kind (.tag ci)) (= 1 (count (:fields wrapper)))
                                     (= (:kind expected) (get {0 :axiom 1 :definition 2 :theorem} kind))
                                     (identical? payload (:payload expected))) "ModuleData CI is not its actually checked published payload")
                          (assoc out name {:ci ci :kind kind :payload payload :info info}))) {} (map vector names infos))]
    (need (= (set names) (set (keys (:payloads version)))) "Source ModuleData omitted a checked local CI")
    {:index index :constant-names (mapv wire-name names) :imports (imports! r scope (aget ^objects fields 0))
     :extra-names (mapv #(wire-name (typed-name scope %)) (array-values r (aget ^objects fields 3) 2048))
     :extensions (mapv (fn [entry]
                         (let [{:keys [fields]} (ordinary r entry 0 2 #{0})]
                           {:name (wire-name (typed-name scope (aget ^objects fields 0)))
                            :entryCount (count (array-values r (aget ^objects fields 1) 16384))}))
                       (array-values r (aget ^objects fields 4) 1024))}))
(defn- check-module-data! [r s]
  (scoped r
    (fn [scope]
      (let [data (root-value (get-in s [:owners :module-data]))
            fs (:fields (ordinary r data 0 5 #{1 8}))
            names (mapv #(typed-name scope %) (array-values r (aget ^objects fs 1) 4096))
            infos (array-values r (aget ^objects fs 2) 4096)
            index (get-in s [:view :source-index])]
        (need (= (count names) (count infos) (count index)) "Source ModuleData domain changed")
        (need (= (mapv wire-name names) (get-in s [:view :metadata :constantNames])) "Source ModuleData constant Names changed")
        (doseq [[name info] (map vector names infos)]
          (let [actual (imported/project-constant-name-kind (:world scope) info {:max-nodes 256 :max-chars 65536} (:carrier-ops scope))
                payload (first (:fields ((:node (:carrier-ops scope)) (:world scope) info))) expected (get index name)]
            (need (and expected (= name (:name actual)) (= (:kind expected) (:kind actual))
                       (identical? info (:info expected)) (identical? payload (:payload expected)))
                  "Source ModuleData CI wrapper/payload changed")))
        (need (= (imports! r scope (aget ^objects fs 0)) (get-in s [:view :metadata :imports])) "Source ModuleData imports changed")))))
(defn- metadata! [text name observed]
  (need (and (string? text) (<= (count text) 1048576)) "Source export metadata exceeds bound")
  (let [m (json/read-str text :key-fn keyword)]
    (need (and (= "lean-source-module/2" (:schema m)) (= "SourceModuleExport.exportClassic" (:producer m))
               (= source/lean-pin (:leanCommit m)) (= "4.33.1" (:leanVersion m))
               (= {:wordBits 64 :target "x86_64-unknown-linux-gnu"} (:runtimeProfile m))
               (= name (:module m)) (false? (:moduleSystem m)) (= "private" (:level m))
               (= "owned-guest-module-data" (:origin m)) (false? (:initializersExecuted m)) (false? (:environmentSerialized m))
               (= "no-local-initializers-exports-externs-redirects/1" (:requirementsPolicy m))
               (= 0 (:localRegularInitCount m) (:localBuiltinInitCount m))
               (= (:imports observed) (:imports m)) (= (:extra-names observed) (:extraConstantNames m))
               (= (:extensions observed) (:extensions m)) (= (:constant-names observed) (:constantNames m))
               (= (count (:index observed)) (:constantCount m)))
          "Actual source ModuleData metadata differs") m))
(defn- captured-module! [borrowed]
  ;; frozen-host descriptions use canonical STRING keys, including sorted maps.
  ;; A keyword lookup against that map is not merely absent: its comparator may
  ;; reject comparing a keyword with a String.
  (let [parts (get (get-in borrowed [:summary :source-description]) "module")]
    (need (and (vector? parts) (<= 1 (count parts) 128) (every? string? parts))
          "Captured actual module segments are missing")
    (reduce (fn [p s] ["str" p s]) ["anonymous"] parts)))
(defn- validate-ci-shapes! [r index]
  ;; Source locals are already Java checked. This readonly projection checks
  ;; that actual export/extension callbacks preserved their full checking shape;
  ;; it does not replay TypeChecker on any imported declaration.
  (scoped r
    (fn [scope]
      (let [projector (imported/make-constant-projector (:world scope) (:carrier-ops scope)
                         {:max-visits 1000000 :max-rule-nodes 10000})]
        (try
          (doseq [[_ {:keys [ci info]}] index]
            (need (= (imported/checking-shape ci)
                     (imported/checking-shape (projector (:world scope) info)))
                  "Exported source CI checking shape differs from its Java checked value"))
          (finally ((:prototype.kernel-bridge/clear-memo! (meta projector)))))))))
(defn export-module!
  "Export only a genuine completed-EOF CommandReceipt whose entire compiler IR
   has been canonically linked. Starts/takes the pinned real guest export helper;
   callers cannot provide ModuleData or Java CIs. Complete failed custody is in
   :operation ex-data. Parent modules are direct ordinary source imports only."
  [runtime receipt generated-scope parent-modules]
  (need (and (vector? parent-modules) (<= (count parent-modules) 16)) "Bounded ordered source parents required")
  (let [rh (issued runtimes runtime) r (runtime! rh)
        parent-data (mapv #(module! % true) parent-modules)
        _ (doseq [p parent-data] (need (identical? rh (:runtime-holder p)) "Foreign source parent runtime"))
        _ (need (= (count parent-data) (count (set (map :module parent-data)))) "Duplicate direct source parent")
        source-holder (#'command/issued @#'command/receipts receipt)
        command-state @source-holder version (:version command-state)
        generated-holder (#'generated/issued @#'generated/scopes generated-scope)
        gs (#'generated/live! generated-holder)
        borrowed (command/with-command! receipt
                   (fn [view]
                     (need (and (= :eoi (get-in view [:source-policy :kind]))
                                (identical? (:engine r) (:engine view)) (identical? (:source r) (:source view))
                                (identical? (:driver gs) (:driver view))
                                (= (:observed-ir gs) (:after-ir view)) (nil? (:pending gs))
                                (= (count (:locals gs)) (count (:after-ir view))))
                           "Module export requires exact completed EOF and wholly linked local IR")
                     (doseq [[n local] (:locals gs)]
                       (need (= (:declaration (get (:after-ir view) n)) (get-in local [:row "ir" "fdecl"])) "Linked IR differs from actual compiler delta"))
                     view))
        [token cell] (operation! runtime)]
    (try
      (let [environment (#'finite/owned source-holder [:after :env])
            name (call! cell :module-name-result "Lean.Environment.mainModule._boxed" [environment])
            _ (retain! cell :module-name name)
            name-wire (scoped r #(wire-name (typed-name % name)))
            expected (captured-module! borrowed)
            _ (need (and (not= ["anonymous"] expected) (= expected name-wire)) "Actual module name differs from captured source module")
            answer (call! cell :export-result "SourceModuleExport.exportClassic._boxed" [environment name 0])
            result-fields (:fields (ordinary r answer 0 1 #{0}))
            pair (:fields (ordinary r (aget ^objects result-fields 0) 0 2 #{0}))
            data (aget ^objects pair 0) text (aget ^objects pair 1)
            _ (retain! cell :module-data data)
            observed (scoped r #(data-index! r % data version))
            metadata (metadata! text name-wire observed)
            expected-imports (mapv (fn [module] {:module module :importAll false :isExported true :isMeta false})
                                   (into [prelude-name] (mapv :module parent-data)))
            _ (need (= expected-imports (:imports observed)) "Actual ModuleData imports differ from exact source parents")
            payload-snapshot ((requiring-resolve 'ansatz.research.ir.source-data-snapshot/capture!)
                               (context r) (:engine r) [data name])
            _ (command/with-command! receipt (fn [view] (need (identical? (:version-marker borrowed) (:version-marker view)) "Export changed checked version")))
            _ (clean! cell #{:module-data :module-name})
            _ ((requiring-resolve 'ansatz.research.ir.source-data-snapshot/validate!) payload-snapshot)
            _ (validate-ci-shapes! r (:index observed))
            _ (command/with-command! receipt (fn [view] (need (identical? (:version-marker borrowed) (:version-marker view)) "Export cleanup changed checked version")))
            _ ((requiring-resolve 'ansatz.research.ir.source-data-snapshot/validate!) payload-snapshot)
            segments (:segments version)
            _ (doseq [segment segments] (snapshot/validate-segment-values segment))
            view {:engine (:engine r) :source (:source r) :module name-wire :data data :name-node name
                  :source-index (:index observed) :snapshot-segments segments :metadata metadata
                  :rows (:locals gs) :parents parent-modules :version-marker (:version-marker borrowed)}]
        (finish! cell)
        ;; Shared holder contains neither Operation nor SourceModule key.
        (reset! cell {:status :sealed :thread (:thread r) :module name-wire :snapshot-segments segments :view view
                      :runtime-holder rh :parents parent-modules
                      :source-holder source-holder :adapter (get-in command-state [:strict-driver :adapter]) :file-retired false
                      :payload-snapshot payload-snapshot :keeper (:keeper @cell)
                      :owners (select-keys (:owners @cell) [:module-data :module-name])})
        (publish! modules (SourceModule.) cell))
      (catch Throwable cause
        (fail! cell cause)
        (throw (ex-info "Source export failed; preserve actual operation owner packet" {:operation token} cause))))))

(defn retire-file!
  "Retire this exported file's actual EOF Run and checked adapter, then release
   its K/map occurrences through the same runtime services. Caller-owned frontend
   InputContext/StateRef/setup roots stay with their original owner journals."
  [source-module actual-command-run]
  (let [module-cell (issued modules source-module) s (module! source-module true)
        source-holder (:source-holder s) session (:adapter s)
        _ (need (and (not (:file-retired s))
                     (identical? source-holder (#'command/issued @#'command/runs actual-command-run)))
                "Exact unretired exported EOF CommandRun required")
        ;; Host idle time is not command work. Rebase before creating an operation
        ;; or changing any retirement custody; failed/running Runs still reject.
        _ (command/rebase-idle-deadline! actual-command-run 60000)
        rh (:runtime-holder s) runtime-token (SourceRuntime.)
        ;; Private temporary key permits normal operation creation without keeping
        ;; a Runtime key anywhere in a registry value.
        _ (publish! runtimes runtime-token rh)
        [token cell] (operation! runtime-token)
        output (object-array 1)]
    (swap! cell assoc :retirement-output output)
    (try
      (command/retire! actual-command-run)
      (let [packet (adapter/take-retirement-owners! session)]
        (aset ^objects output 0 packet)
        (doseq [[i value] (map-indexed vector packet)]
          (#'lineage/new-owner! cell [:association-retirement i] value :owned))
        (clean! cell #{})
        (finish! cell)
        (swap! module-cell #(-> % (assoc :file-retired true) (dissoc :source-holder :adapter)))
        {:status :retired :association-occurrences (count packet)})
      (catch Throwable cause
        (fail! cell cause)
        (throw (ex-info "Source file retirement failed; preserve both owner journals"
                       {:operation token :command-run actual-command-run} cause))))))

(defn with-closure!
  "Scoped facade for the separately loaded source-closure issuer."
  [token callback]
  ((requiring-resolve 'java-source-closure-v1/with-closure!) token callback))
(defn with-finalized!
  "Borrow only actual source-closure start/take lineage."
  [token callback]
  ((requiring-resolve 'java-source-closure-v1/with-finalized!) token callback))

(defn take-operation-retirement-owners!
  "Explicit transfer for a FAILED operation at a known idle, taken-result
   boundary only. Pending/ambiguous retains, starts, takes or releases reject.
   This does not retry/unwind execution or reopen the failed Runtime."
  [operation]
  (let [cell (issued operations operation) s @cell r @(:runtime-holder s)
        ctx (context r) engine (:engine r)
        known #{:owned :transferred :released :immediate-consumed}]
    (need (and (= :failed (:status s)) (identical? (:thread s) (Thread/currentThread))
               (nil? (:call s)) (nil? (:release s)) (= "idle" (j/phase ctx engine))
               (identical? (:program ctx) (field engine "program"))
               (every? #(false? (field engine %)) ["closed" "disposed" "untrackedFailure" "advancing"])
               (every? #(contains? known (root-state %)) (vals (:owners s))))
          "Failed operation has pending/unknown ownership or is not a healthy idle boundary")
    (source/guard-source! (:code-receipt r) (:source r))
    (module/inspect! (:module-lease r)) (lineage/inspect! (:prelude-run r))
    (let [owned (vec (filter (fn [[_ slot]] (= :owned (root-state slot))) (:owners s)))
          packet (mapv (fn [[_ slot]] (root-value slot)) owned)
          output (object-array [packet])]
      ;; Publish the exact output table BEFORE committing occurrence transfers.
      (swap! cell assoc :retirement-output output :status :retirement-prepared)
      (doseq [[_ slot] owned] (aset ^objects slot 1 :external-retirement))
      (reset! cell {:status :retired :retirement-output output})
      packet)))

(defn- known-owned-slots! [r slots]
  (let [ctx (context r) engine (:engine r)]
    (need (and (identical? (:thread r) (Thread/currentThread))
               (nil? (:active r)) (= "idle" (j/phase ctx engine))
               (identical? (:program ctx) (field engine "program"))
               (every? #(false? (field engine %)) ["closed" "disposed" "untrackedFailure" "advancing"])
               (every? #(contains? #{:owned :transferred :released :immediate-consumed :external-retirement}
                                  (root-state %)) slots))
          "Source owner retirement requires known slots and healthy idle custody")
    (source/guard-source! (:code-receipt r) (:source r))
    (filterv #(= :owned (root-state %)) slots)))
(defn take-module-retirement-owners!
  "Revoke one module and transfer its two authoritative owner occurrences.
   Dependent module/closure borrows subsequently fail. Reverse dependency cleanup
   order remains caller-owned; this does not discharge caller's frontend owners."
  [source-module]
  (let [cell (issued modules source-module) s (module! source-module true)
        r (runtime! (:runtime-holder s))
        _ (need (:file-retired s) "Retire the exported file/adapter before its module owners")
        owned (known-owned-slots! r (vec (vals (:owners s))))
        packet (mapv root-value owned) output (object-array [packet])]
    (swap! cell assoc :retirement-output output :status :retirement-prepared)
    (doseq [slot owned] (aset ^objects slot 1 :external-retirement))
    (reset! cell {:status :retired :module (:module s) :retirement-output output})
    packet))
(defn take-runtime-retirement-owners!
  "Terminal transfer of this runtime's known source-operation/module/closure
   owners only. Revoke adapters/Base views first. Borrowed original Prelude
   Module/Run/store/frontend/runtime-provider owners remain separate."
  [runtime]
  (let [rh (issued runtimes runtime) r @rh
        _ (need (contains? #{:open :failed} (:status r)) "Source runtime was already retired")
        slots (java.util.IdentityHashMap.)
        _ (doseq [keeper (:keepers r) slot (vals @(:owners keeper))] (.put slots slot true))
        owned (known-owned-slots! r (vec (.keySet slots)))
        packet (mapv root-value owned) output (object-array [packet])]
    ;; Slot identity deduplicates journals for one occurrence transferred between
    ;; operations/closures/Runs; distinct slots aliasing one Node stay distinct.
    (swap! rh assoc :retirement-output output :status :retirement-prepared)
    (doseq [slot owned] (aset ^objects slot 1 :external-retirement))
    (locking modules
      (doseq [entry (.entrySet modules) :let [cell (.getValue ^java.util.Map$Entry entry)]
              :when (identical? rh (:runtime-holder @cell))]
        (reset! cell {:status :retired :module (:module @cell)})))
    (locking operations
      (doseq [entry (.entrySet operations) :let [cell (.getValue ^java.util.Map$Entry entry)]
              :when (identical? rh (:runtime-holder @cell))]
        (reset! cell {:status :retired})))
    (when-let [namespace (find-ns 'java-source-closure-v1)]
      (when-let [revoke (ns-resolve namespace 'revoke-runtime-metadata!)] (revoke rh)))
    (reset! rh {:status :retired :retirement-output output})
    packet))

(defn close-runtime!
  "Drop retired host metadata. For an already normally disposed/closed engine,
   permit compaction only when every recorded source occurrence was discharged
   or transferred. Does not dispose an engine or close borrowed resources."
  [runtime]
  (let [rh (issued runtimes runtime) r @rh]
    (when (= :retired (:status r)) (reset! rh {:status :closed}))
    (when-not (contains? #{:retired :closed} (:status r))
      (need (and (identical? (:thread r) (Thread/currentThread)) (nil? (:active r))
                 (or (true? (field (:engine r) "disposed")) (true? (field (:engine r) "closed"))))
            "Source runtime metadata close requires actual completed engine disposal")
      (need (every? (fn [keeper]
                      (every? #(contains? #{:transferred :released :immediate-consumed :external-retirement} (root-state %))
                              (vals @(:owners keeper)))) (:keepers r))
            "Source runtime still owns or cannot account for a guest occurrence")
      (reset! rh {:status :closed}))) nil)
