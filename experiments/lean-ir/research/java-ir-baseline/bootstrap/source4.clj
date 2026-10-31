(ns ansatz.research.ir.bootstrap.source4
  "Fresh explicit-Prelude Source4 composition and lifecycle over tracked units.
   No ambient user Vars, temporary CodeReceipt, compose interception, synthetic
   initialization success or automatic failed-owner unwinding."
  (:require [clojure.java.io :as io] [clojure.data.json :as json] [clojure.edn :as edn]
            [ansatz.research.ir.bootstrap.artifacts :as artifacts]
            [ansatz.research.ir.bootstrap.definitions :as definitions]
            [ansatz.research.ir.bootstrap.captured-runtime :as captured]
            [ansatz.research.ir.bootstrap.policies :as policies]
            [ansatz.research.ir.bootstrap.policies-early :as early]
            [ansatz.research.ir.catalogue :as cat] [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.composite-source-v4 :as composite]
            [ansatz.research.ir.authenticated-demand :as demand]
            [java-ir-baseline :as j] [sequential-frontend-probe :as sp]
            [allocation-heartbeat-cohort-v1 :as cohort] [authenticated-raw-row-cache-v1 :as cache]
            [original-runtime-limits-provider-v1 :as limits] [original-stdin-configuration-v1 :as stdin]
            [java-matched-prelude-module-v4 :as module] [general-frontend-file-v1 :as file])
  (:import [java.util WeakHashMap] [java.nio.file Files LinkOption]
           [java.nio.charset CodingErrorAction StandardCharsets] [java.security MessageDigest]))
(deftype Bootstrap [])
(defonce ^:private bootstraps (WeakHashMap.))
(def modules ["KernelBridgeShim" "JavaModuleImport" "ObservedFrontendCommand" "SourceModuleExchange"])
(def row-counts [252 28 16 271])
(def source-pins [(get composite/shim-pins "source_sha256") (get composite/module-pins "source_sha256")
                  "291b8dbe2298fa2e9310417294a2c442b1f4849f317f07405048c05dce585e27"
                  "54b0a48c3ca041a8ebeddcdee7fa1f23f425bd07b470df6537c03d49e74ee88d"])
(def extra-helpers ["KernelBridgeShim.postCheckDefinition._boxed" "KernelBridgeShim.postCheckSafeOpaque._boxed"
                    "KernelBridgeShim.postCheckMutualDefinitions._boxed" "KernelBridgeShim.postCheckGeneratedFamily._boxed"])
(def gate-sha "bf96d5878e30e9e49eaf2b451742599e044afaaaea7f16423a9653fe6f49ecb9")
(defn- need [ok message] (when-not ok (throw (ex-info message {:component :source4-bootstrap}))))
(defn- field [x name] (.get (doto (.getDeclaredField (class x) name) (.setAccessible true)) x))
(defn- entry [token]
  (locking bootstraps (or (.get bootstraps token) (throw (ex-info "Actual Source4 Bootstrap required" {})))))
(defn- failure [error]
  {:class (.getName (class error)) :message (subs (or (.getMessage error) "Bootstrap failed") 0
                                             (min 800 (count (or (.getMessage error) "Bootstrap failed"))))})
(defn- profile! [profile]
  (let [p (artifacts/description profile)]
    (need (every? #(contains? p %) ["runtime" "catalogue" "capture" "policies" "lean-source" "layout-directory"
                                    "matched" "externs" "evidence" "enabled-admissions" "budgets" "definitions"])
          "Complete Source4 profile required before any resource opens")
    (doseq [[key fields] [["runtime" #{"jar" "source" "build-receipt" "task-profile" "graph-profile" "stdio-profile" "native-init-profile"}]
                          ["catalogue" #{"manifest" "cas-root"}] ["capture" #{"manifest" "source" "capsule" "headers" "directory" "census"}]
                          ["policies" #{"index" "fixture-directories"}] ["lean-source" #{"commit" "files"}]
                          ["matched" #{"pair-directory" "store-directory" "store-manifest"}]
                          ["externs" #{"directory" "manifest"}] ["evidence" #{"observed-contract" "observed-layout"}]]]
      (need (= fields (set (keys (get p key)))) "Bootstrap field set differs from supported profile"))
    (let [budget (get p "budgets")]
      (need (and (= #{"commands" "code-requests" "instructions" "turns"} (set (keys budget)))
                 (every? #(and (integer? %) (pos? %)) (vals budget))
                 (<= (get budget "commands") 128) (<= (get budget "code-requests") 20000)
                 (<= (get budget "instructions") 50000000) (<= (get budget "turns") 1000000))
            "Explicit bounded frontend budgets required before image construction"))
    (let [runtime (get p "runtime") receipt (artifacts/json! profile (get runtime "build-receipt") 65536)]
      (need (and (= "java-ir-runtime-build/1" (get receipt "schema"))
                 (= 11 (get receipt "java-release")) (= source/lean-pin (get receipt "lean-commit"))
                 (= "x86_64-unknown-linux-gnu" (get receipt "target"))
                 (= (get-in p ["artifacts" (get runtime "jar") "sha256"]) (get receipt "jar-sha256"))
                 (= (get-in p ["artifacts" (get runtime "source") "sha256"]) (get receipt "source-sha256")))
            "Pinned runtime jar/source/build receipt differs"))
    (doseq [i (range 4)]
      (let [o (nth (get p "overlays") i)]
        (need (and (= #{"directory" "source" "producer" "module" "row-count" "pins" "actions"} (set (keys o)))
                   (= ["str" ["anonymous"] (nth modules i)] (get o "module"))
                   (= (nth row-counts i) (get o "row-count"))
                   (= (nth source-pins i) (get-in o ["pins" "source_sha256"]))
                   (= composite/index-sha (get-in o ["pins" "base_index_sha256"]))
                   (= composite/producer-sha (get-in o ["pins" "producer_sha256"]))
                   (= source/lean-pin (get-in o ["pins" "lean_commit"]))
                   (= (if (= i 1) composite/actions []) (get o "actions")))
              "Source4 requires the exact ordered reviewed overlay family")))
    (need (and (= "logical-sync-ready-and-pending/1" (get-in p ["runtime" "task-profile"]))
               (= "persistent-ref-payload-mt/1" (get-in p ["runtime" "graph-profile"]))
               (= "logical-single-engine-thread/1" (get-in p ["runtime" "stdio-profile"]))
               (= "empty-native-module-symbol-table/1" (get-in p ["runtime" "native-init-profile"]))
               (= ["axiom" "theorem" "safe-definition" "compiler-generated-mutual-definition"]
                  (get p "enabled-admissions")))
          "Unsupported runtime/admission profile")
    p))
(defn- configured-context [bundle catalogue receipt ctx src existing]
  (let [configured (policies/prepare-import-context ctx src existing
                     {:receipt receipt :catalogue catalogue :policies bundle})
        by-sha (atom (merge existing (:headers-by-sha configured)))
        header! (fn [name]
                  (let [{:keys [row sha256]} (source/lookup-entry receipt name)
                        _ (need row "Missing authenticated context row")
                        h (or (get @by-sha sha256) (j/declaration-header src row sha256))]
                    (source/authenticate-canonical-header! src row sha256 h)
                    (swap! by-sha assoc sha256 h) h))
        extra (into {} (map (fn [label] [label (header! (sp/typed-name label))]) extra-helpers))
        gate (header! (sp/typed-name "ObservedFrontendCommand.beforeElaboration"))
        parser (header! (sp/typed-name "Lean.MessageLog.hasErrors._boxed"))
        wire (fn [parts] (reduce (fn [p x] (if (integer? x) ["num" p (str x)] ["str" p x])) ["anonymous"] parts))
        pairs (mapv (fn [leaf]
                      [(header! (wire ["_private" "Lean" "Environment" 0 "Lean" leaf]))
                       (header! (wire ["_private" "Lean" "Compiler" "IR" "CompilerM" 0 "Lean" "IR" leaf]))])
                    ["exportIREntries" "getIRExtraConstNames"])
        _ (need (= gate-sha (j/request-value gate "originalSha256")) "Observer gate is not the reviewed source")
        registered (j/register-headers (:ctx configured) (vec (distinct (concat [gate parser] (vals extra) (mapcat identity pairs)))))
        ready (j/bind-guest-exports registered pairs)
        helpers (merge (:helper-headers configured) extra) outer (conj (vec (:outer-headers configured)) gate)
        policy (j/host-guest-policy ready outer (conj (vec (vals helpers)) parser))]
    (assoc configured :ctx ready :headers-by-sha @by-sha :helper-headers helpers :outer-headers outer
           :observed-gate-header gate :observed-parser-errors-header parser :source-module-export-pairs pairs
           :configure-engine! (fn [ctx engine] (j/configure-host-guest! ctx engine policy)))))
(defn authenticate!
  "BASIS is the caller-owned actual jar basis. JOURNAL must be fresh and is
   published before opening the first catalogue/resource. Failure returns no
   success token; the thrown data preserves this issued bootstrap/journal.
   Artifact Profile and basis classloader remain caller-owned."
  [profile basis journal]
  (need (and (instance? clojure.lang.IAtom journal) (= {} @journal)) "Fresh explicit bootstrap journal required")
  (need (and (nil? (:program basis)) (empty? (:early-host-specifications basis))
             (nil? (:task-runtime basis)) (nil? (:build-identity basis)) (nil? (:profiling-policy basis)))
        "Supply the raw same-jar class basis, not an old configured context or policy")
  (let [p (profile! profile) jar (artifacts/file! profile (get-in p ["runtime" "jar"]))
        _ (definitions/assert-basis! basis jar)
        holder (atom {:status :authenticating :thread (Thread/currentThread) :profile profile :basis basis :journal journal :children []})
        token (Bootstrap.) catalogue-slot (object-array [nil :open-pending])]
    (locking bootstraps (.put bootstraps token holder))
    (swap! journal assoc :stage :catalogue-open-pending :catalogue catalogue-slot)
    (try
      (let [c (get p "catalogue")
            catalogue (cat/open (artifacts/file! profile (get c "manifest"))
                        {:expected-manifest-sha256 (get-in p ["artifacts" (get c "manifest") "sha256"])
                         :expected-source-index-sha256 composite/index-sha
                         :cas-root (artifacts/root! profile (get c "cas-root")) :max-blob-bytes 8388608})
            _ (aset catalogue-slot 0 catalogue) _ (aset catalogue-slot 1 :owned)
            _ (swap! holder assoc :catalogue catalogue)
            _ (swap! journal assoc :stage :policy-authentication)
            fixtures (into {} (for [[id group] (get-in p ["policies" "fixture-directories"])]
                                [id (artifacts/directory! profile group)]))
            bundle (policies/authenticate-policies! {:catalogue catalogue :fixtures fixtures
                                                     :index-file (artifacts/file! profile (get-in p ["policies" "index"]))
                                                     :lean-source (artifacts/source-reader profile)})
            setup (policies/setup-evidence! catalogue {:policies bundle})
            captured-source (artifacts/json! profile (get-in p ["capture" "source"]) 1048576)
            overlays (mapv (fn [o]
                             (source/authenticate-overlay! catalogue (artifacts/directory! profile (get o "directory"))
                               {:source-file (artifacts/file! profile (get o "source"))
                                :producer-file (artifacts/file! profile (get o "producer"))
                                :module (get o "module") :row-count (get o "row-count") :pins (get o "pins") :actions (get o "actions")}))
                          (get p "overlays"))
            setup (update setup :evidence-pins merge
                    {"observed_frontend_contract_sha256" (get-in p ["artifacts" (get-in p ["evidence" "observed-contract"]) "sha256"])
                     "observed_frontend_layout_sha256" (get-in p ["artifacts" (get-in p ["evidence" "observed-layout"]) "sha256"])
                     "source_module_exchange_source_sha256" (nth source-pins 3)})
            _ (need (= composite/helpers (:helpers setup)) "Fixed eight setup helpers must remain exact")
            _ (swap! journal assoc :stage :compose-pending)
            receipt (source/compose! catalogue captured-source overlays setup)
            _ (swap! holder assoc :receipt receipt :policies bundle)
            _ (swap! journal assoc :stage :capture-preflight :code-receipt receipt)
            capture (captured/preflight! profile receipt)
            _ (swap! holder assoc :capture capture)
            _ (artifacts/guard! profile)]
        (swap! holder assoc :status :authenticated)
        (swap! journal assoc :stage :authenticated)
        token)
      (catch Throwable error
        (swap! holder assoc :status :failed :failure (failure error))
        (throw (ex-info "Bootstrap authentication failed; preserve its actual resource journal"
                        {:bootstrap token :journal @journal} error))))))
(defn- live! [holder]
  (let [s @holder]
    (need (and (contains? #{:authenticated :ready} (:status s)) (identical? (:thread s) (Thread/currentThread)))
          "Bootstrap is terminal or foreign-thread")
    (artifacts/guard! (:profile s))
    (cat/source-token (:catalogue s))
    s))
(defn open-parent!
  "Construct exactly one pristine parent from a fully authenticated profile.
   Any construction failure is terminal for this bootstrap; no retry/rollback."
  [token]
  (let [holder (entry token) s (live! holder)
        _ (need (= :authenticated (:status s)) "Parent construction may be attempted only once")
        journal (:journal s)]
    (swap! holder assoc :status :opening)
    (swap! journal assoc :stage :parent-metadata-preflight)
    (try
      (let [profile (:profile s) p (artifacts/description profile) receipt (:receipt s) bundle (:policies s)
        c (:catalogue s)
        extern (get p "externs")
        derived (early/derive! bundle (:basis s) receipt {:catalogue c
                    :extern-directory (artifacts/directory! profile (get extern "directory"))
                    :extern-manifest-sha256 (get-in p ["artifacts" (get extern "manifest") "sha256"])})
        extras (mapv #(select-keys % ["module" "source_sha256" "local_ir_sha256" "export_receipt_sha256" "producer_sha256" "base_index_sha256"])
                     (drop 2 (get (source/code-profile receipt) "overlays")))
        rows (cache/open-policy receipt)
        policy-journal (atom {})
        _ (swap! holder assoc :row-policy rows :policy-journal policy-journal)
        _ (swap! journal assoc :stage :parent-opening :row-policy rows :policy-configuration policy-journal)
        configured (assoc (:basis s) :explicit true :task-runtime (j/logical-sync-task-runtime (:basis s))
                     :build-identity (j/supported-build-identity (:basis s)) :graph-import-profile :persistent-ref-payload-mt
                     :early-host-specifications (conj (vec (:additional-early-host-specifications derived)) (:gate-specification derived))
                     :accepted-code-profile (fn [actual]
                                              (need (= actual (get (source/code-profile receipt) "captured_graph_source")) "Foreign capture description")
                                              (source/code-profile receipt))
                     :source-binding-factory (fn [ctx accepted]
                                               (need (identical? accepted (source/code-profile receipt)) "Foreign source-code profile")
                                               (source/source-binding! ctx receipt))
                     :configure-import-context (fn [ctx src existing] (configured-context bundle c receipt ctx src existing)))]
      (let [parent (cohort/open-parent! configured receipt
                     (artifacts/directory! profile (get-in p ["capture" "directory"]))
                     {:journal journal :census! captured/selected-heap-census
                      :open-companion! (fn [basis dir expected census! journal]
                                         (captured/open! (:capture s) basis dir expected census! journal))
                      :layout-directory (.getPath (artifacts/directory! profile (get p "layout-directory")))
                      :open-driver! (fn [live]
                                      (let [memo (into {} (for [[sha h] (:headers-by-sha live)]
                                                           [(demand/exact-name-key (j/request-value h "name")) {:header h :sha256 sha}]))
                                            d (assoc live :catalogue c :current-ctx (atom (:ctx live)) :headers-by-name (atom memo) :requests (atom []))]
                                        (demand/attach d rows)))
                      :configure! (fn [driver] (policies/configure! driver {:receipt receipt :catalogue c :policies bundle :journal policy-journal}))
                      :additional-runtime-service {:handles? limits/handles? :serve! (fn [session] (limits/serve! receipt session))}
                      :configure-child! stdin/configure-child!})
            actual (assoc parent :extra-code-overlays extras)]
        (need (and (zero? (j/instructions @(:current-ctx (:driver actual)) (get-in actual [:driver :engine])))
                   (= :pending (:state @(:startup-status actual)))) "Seed must remain pristine")
        (swap! holder assoc :status :ready :parent actual)
        (swap! journal assoc :parent actual :stage :ready)
        actual))
      (catch Throwable error
        (swap! holder assoc :status :failed :failure (failure error))
        (throw (ex-info "Source4 parent construction failed; preserve its actual resource journal"
                        {:bootstrap token :journal @journal} error))))))
(defn prepare-module!
  "Prepare the fixed paired Prelude through its existing seven-file verifier and
   converter. No install or guest finalization. Reusable only on this class basis."
  [token]
  (let [holder (entry token) s (live! holder) p (artifacts/description (:profile s))]
    (need (and (= :ready (:status s)) (nil? (:prepared-module s))) "Module preparation is once per bootstrap")
    (swap! holder assoc :status :module-preparing)
    (swap! (:journal s) assoc :stage :module-prepare-pending)
    (try
      (let [prepared (module/prepare! @(:current-ctx (get-in s [:parent :driver]))
                                     (artifacts/directory! (:profile s) (get-in p ["matched" "pair-directory"])))]
        (swap! holder assoc :status :ready :prepared-module prepared)
        (swap! (:journal s) assoc :stage :ready :prepared-module prepared)
        prepared)
      (catch Throwable error
        (swap! holder assoc :status :failed :failure (failure error))
        (throw (ex-info "Module preparation failed; preserve bootstrap journal" {:bootstrap token :journal @(:journal s)} error))))))
(defn- capture! [capture]
  (need (and (map? capture) (string? (:text capture)) (instance? java.nio.file.Path (:path capture))
             (vector? (:module capture)) (<= 1 (count (:module capture)) 128)
             (every? #(and (string? %) (<= 1 (count %) 4096)
                           (not-any? (set (map char [46 47 92 0])) %)) (:module capture))) "Bounded source capture required")
  (let [text (:text capture) bytes (.getBytes ^String text StandardCharsets/UTF_8)]
    (need (and (<= (alength bytes) 65536) (= text (String. bytes StandardCharsets/UTF_8))
               (= (alength bytes) (:byte-count capture))
               (= (:sha256 capture) (apply str (map #(format "%02x" (bit-and 255 %)) (.digest (MessageDigest/getInstance "SHA-256") bytes)))))
          "Source capture bytes/digest differ"))
  capture)
(defn prepare-child!
  "Fresh same-basis general512 branch with actual module/startup/finalizer/Base.
   Journal is published before fork, and retained on every partial failure."
  [token capture journal]
  (let [holder (entry token) s (live! holder) capture (capture! capture)
        _ (need (and (= :ready (:status s)) (:prepared-module s)
                     (instance? clojure.lang.IAtom journal) (= {} @journal)) "Ready parent/prepared module/fresh child journal required")
        p (artifacts/description (:profile s)) matched (get p "matched")
        child-slot (object-array 1) engine-slot (object-array 1)
        child-record {:journal journal :child-slot child-slot :engine-slot engine-slot}
        store {:path (artifacts/directory! (:profile s) (get matched "store-directory"))
               :manifest (edn/read-string (String. ^bytes (artifacts/bytes! (:profile s) (get matched "store-manifest") 65536)
                                                          StandardCharsets/UTF_8))
               :layout-directory (.getPath (artifacts/directory! (:profile s) (get p "layout-directory")))
               :observe-child! (fn [actual]
                                 ;; Called only from the trusted factory's actual
                                 ;; child local. Never publish these latch arrays
                                 ;; or this callback in a caller-owned journal.
                                 (aset ^objects child-slot 0 actual)
                                 (aset ^objects engine-slot 0 (get-in actual [:driver :engine])))}
        budget (get p "budgets")]
    (need (and (= #{"commands" "code-requests" "instructions" "turns"} (set (keys budget)))
               (every? #(and (integer? %) (pos? %)) (vals budget))
               (<= (get budget "commands") 128) (<= (get budget "code-requests") 20000)
               (<= (get budget "instructions") 50000000) (<= (get budget "turns") 1000000))
          "Explicit bounded frontend budgets required")
    (swap! holder update :children conj child-record)
    (cohort/prepare-general-source-child! journal (:parent s) (:prepared-module s)
                                        (:text capture) (str (:path capture)) (:module capture) store)
    (swap! journal update :frontend update :limits merge (into {} (map (fn [[k v]] [(keyword k) v])) budget))
    @journal))
(defn open-file! [token capture journal]
  (let [s (live! (entry token)) bundle (prepare-child! token capture journal) d (get-in bundle [:child :driver])
        headers (into {} (for [[role label] [[:entry "ObservedFrontendCommand.processCommandObserved._boxed"]
                                             [:caller "ObservedFrontendCommand.processCommandObserved"]
                                             [:gate "ObservedFrontendCommand.beforeElaboration"]
                                             [:parser-errors "Lean.MessageLog.hasErrors._boxed"]]]
                           [role (demand/ensure-header! d (sp/typed-name label))]))
        ready (j/register-headers @(:current-ctx d) (vec (vals headers)))]
    (j/install-program! ready (:engine d)) (reset! (:current-ctx d) ready)
    (let [run (file/open-file! bundle capture
                {:headers headers :layout-directory (:layout-directory (:parent s))
                 :close-branch! (fn [actual]
                                  (need (and (identical? (:child bundle) (:child actual))
                                             (identical? (:admission bundle) (:admission actual))) "Foreign branch close")
                                  (swap! journal merge actual)
                                  (cohort/retire-source-child! journal))})]
      (swap! journal assoc :file run) run)))
(defn warm-original-code!
  "Optional metadata-only original bodies. Reauthenticate Name/SHA under THIS
   catalogue/receipt; never promote generated rows or execute an initializer."
  [token entries]
  (let [s (live! (entry token)) d (get-in s [:parent :driver]) e (:engine d) before (j/instructions @(:current-ctx d) e)]
    (need (and (= :ready (:status s)) (vector? entries) (<= (count entries) 20000)
               (= "idle" (j/phase @(:current-ctx d) e)) (zero? before)) "Warm only pristine original seed")
    (doseq [{:keys [name sha256]} entries]
      (let [entry (cat/lookup (:catalogue s) name) row (:row entry)
            _ (need (and (= sha256 (:sha256 entry)) (get-in row ["ir" "fdecl"])) "Warm row is not authenticated original code")
            h (demand/ensure-header! d name) deps (mapv #(demand/ensure-header! d %) (demand/direct-names row))
            ready (j/materialize-body @(:current-ctx d) h row deps)]
        (j/install-program! ready e) (reset! (:current-ctx d) ready)))
    (need (= before (j/instructions @(:current-ctx d) e)) "Warmup executed guest instructions")
    {:status :original-code-prepared :rows (count entries) :guest-instructions 0}))
(defn owner-packet [token]
  (let [s @(entry token)]
    {:status (:status s) :failure (:failure s) :journal @(:journal s)
     :children (mapv (fn [record] {:journal @(:journal record)
                                  :engine (aget ^objects (:engine-slot record) 0)}) (:children s))}))
(defn close-authenticated!
  "Close a successful metadata-only bootstrap BEFORE its one parent attempt.
   No engine or SourceBinding has been constructed. Input Profile/basis remain
   caller-owned. This is not failed-engine cleanup or rollback."
  [token]
  (let [holder (entry token) s (live! holder)]
    (need (= :authenticated (:status s)) "Only unstarted authenticated metadata may close here")
    (cat/close! (:catalogue s))
    (reset! (:journal s) {:stage :closed-before-parent})
    (reset! holder {:status :retired :thread (:thread s) :retirement :closed-before-parent})
    nil))
(defn- retired-child! [s record]
  (let [child (aget ^objects (:child-slot record) 0) engine (aget ^objects (:engine-slot record) 0)]
    (need (and child engine
               (identical? engine (get-in child [:driver :engine]))
               (identical? (get-in s [:parent :driver :source]) (get-in child [:driver :source]))
               (true? (field engine "disposed")) (true? (field engine "closed"))
               (= :disposed-and-closed (get-in @(:journal record) [:retirement :status])))
          "Actual privately captured child must be disposed and closed")
    nil))
(defn retire!
  "Normal seed retirement only after every child journal reports actual complete
   retirement. Failed operations remain preserved, never discarded by this API."
  [token]
  (let [holder (entry token) s (live! holder)]
    (need (= :ready (:status s)) "Ready bootstrap required for normal seed retirement")
    (doseq [record (:children s)] (retired-child! s record))
    (let [result (cohort/retire-engine! (:parent s) [])]
      ((:close! (:row-policy s))) (cat/close! (:catalogue s))
      (reset! (:journal s) {:stage :retired :retirement result})
      (reset! holder {:status :retired :thread (:thread s) :retirement result})
      result)))
