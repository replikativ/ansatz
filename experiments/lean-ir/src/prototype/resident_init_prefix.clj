(ns prototype.resident-init-prefix
  "Optional checked-Init prefix preparation and staged over-Init source imports.
   The original successful CHECKED result is a TRUSTED host input. Issuing an
   opaque prefix does not authenticate the provenance of a caller-created map.
   Context branches own guest roots; native Stores and catalogues stay borrowed."
  (:require [prototype.resident-frontend :as resident]
            [prototype.resident-source :as publication]
            [prototype.runtime-string :as string]
            [prototype.runtime-prim :as prim]
            [clojure.data.json :as json]
            [prototype.source-import :as source]
            [prototype.source-graph-plan :as graph-plan]
            [prototype.kernel-host :as kernel-host]
            [prototype.module-import :as imports]
            [prototype.module-store :as store]
            [prototype.eval-const :as eval]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
            [prototype.kernel-bridge :as bridge]
            [prototype.constructor-layout :as constructor]
            [prototype.imported-kernel :as imported]
            [prototype.native-scalar :as native]
            [prototype.frontend :as frontend]
            [prototype.guest-encoding :as encoding]
            [prototype.globals-consumer-factory :as native-factory]
            [prototype.resident-import :as standalone]
            [ansatz.kernel.name :as name]
            [clojure.string :as str])
  (:import [ansatz.kernel Env ConstantInfo]
           [java.util WeakHashMap]
           [java.util.concurrent.atomic AtomicBoolean]))

(deftype InitPrefix [])
(defonce ^:private issued (WeakHashMap.))
(defn- fail [message data] (throw (ex-info message data)))
(defn- capability! [value]
  (or (locking issued (.get issued value))
      (fail "Expected an issued resident Init prefix" {})))

(def preparation-roots
  "Fixed sequential native assembly and future hybrid/finalizer/checking roots.
   All must match independently captured preparation before any guest call."
  (vec (distinct (concat (vals imports/helpers) (vals source/helpers)
                         [source/hybrid-assemble-helper]))))

(defn- preparation-readiness!
  "Host-only checks. CONFIGURATION and NATIVE-BINDINGS are independently captured
   trusted host inputs. Routing must already be prepared: this API changes no
   binding. Only read/free/evalConst may differ from the original native registry;
   in particular the original native initializer callback is preserved exactly."
  [prepared configuration native-bindings]
  (resident/adoption-readiness! prepared configuration)
  (eval/validate-executables! (:world prepared) (:trusted-functions configuration) preparation-roots)
  ;; This public constructor validates required native signatures and handlers.
  ;; Its fresh closures are discarded; installed closures are authenticated by
  ;; the independent configuration, not by equality with a newly built registry.
  (source/make-hybrid-bindings native-bindings)
  (let [actual (get-in prepared [:session :bindings])
        replaced #{"lean_compacted_region_read" "lean_compacted_region_free" "lean_eval_const"}]
    (when-not (= (set (keys actual)) (set (keys native-bindings)))
      (fail "Init prefix native and prepared binding registries differ" {}))
    (doseq [[symbol binding] native-bindings :when (not (contains? replaced symbol))]
      (when-not (identical? binding (get actual symbol))
        (fail "Init prefix native capability changed" {:symbol symbol})))
    (doseq [symbol ["lean_compacted_region_read" "lean_compacted_region_free"]]
      (when-not (and (= (:signature (get native-bindings symbol)) (:signature (get actual symbol)))
                     (fn? (:handler (get actual symbol))))
        (fail "Init prefix hybrid routing signature changed" {:symbol symbol}))))
  true)

(defn- checked! [entry checked]
  (let [world (:world entry) original (:world checked) certificate (:certificate checked)
        ^Env env (:env certificate) sources (:projection-sources certificate)
        constants (:constants certificate) projected (:projected certificate)]
    (when-not (and (= :ok (:status checked)) (= (:environment entry) (:environment checked))
                   (map? original) (instance? Env env) (map? constants) (map? projected)
                   (= (set (keys constants)) (set (keys projected)))
                   (= 1 (count sources)) (= 1 (count (:native-imports world)))
                   (identical? (first sources) (first (:native-imports world)))
                   (= 1 (count (:native-imports original)))
                   (identical? (first sources) (first (:native-imports original))))
      (fail "Init prefix requires the original checked result and exact attached Source" {}))
    (let [actual (.allConstants env)]
      (when-not (and (= (count actual) (count projected))
                     (every? (fn [^ConstantInfo ci] (identical? ci (get projected (.name ci)))) actual))
        (fail "Init prefix checked ConstantInfo identities differ" {})))
    (doseq [[_ value] constants]
      (when-not (and (m/ref? value)
                     (or (m/native-reference? world value)
                         (let [before (get-in original [:heap (:id value)])
                               after (get-in world [:heap (:id value)])]
                           (and before after (= (dissoc before :rc) (dissoc after :rc))))))
        (fail "Init prefix checked guest constant changed" {})))
    certificate))

(defn- packet [entry world session]
  ;; A new Context does not carry a checking certificate in evolving metadata.
  {:world world :session session :environment (:environment entry)
   :options (:options entry) :catalogue (:catalogue entry)})

(defn prepare-init-prefix
  "Prepare a checked native Init prefix in a NEW persistent resident branch.
   CHECKED must be the original successful checking result for this Context's
   Environment, supplied by trusted host code. OPTIONS is exactly
   {:configuration independent-resident-config :native-bindings original-native}.
   No source reopening/bootstrap, initializer replay or binding replacement.
   Return {:context new-context :prefix issued-capability :receipt descriptive-data}.

   The world registry owns the prefix state; the capability borrows it and keeps
   the original certificate privately. Env/Options ownership follows resident/fork:
   the new branch inherits its existing owners without retain/drop churn. Input
   remains unchanged/open. Failure retains terminal exact packets, not a retry or
   cleanup capability; the borrowed Store/lease must outlive retained branches."
  [context checked {:keys [configuration native-bindings] :as options}]
  (locking context
    (let [entry (resident/snapshot context) active (atom (:session entry))
          progress (volatile! (:world entry)) phase (volatile! :entry)
          prepared (volatile! nil) last-call (volatile! nil)
          invoke (fn [world target args]
                   (vreset! progress world)
                   (let [called (raw/call @active world target args)]
                     (vreset! last-call {:target target :arguments args :returned called})
                     (reset! active (:session called)) (vreset! progress (:state called))
                     [(:state called) (:value called)]))]
      (try
        (when-not (and (map? options) (= #{:configuration :native-bindings} (set (keys options)))
                       (map? configuration) (map? native-bindings))
          (fail "Init prefix requires explicit independent configuration and original native bindings" {}))
        (preparation-readiness! entry configuration native-bindings)
        (let [certificate (checked! entry checked)
              loaded (store/describe-attached @progress (first (:projection-sources certificate)))]
          (vreset! phase :prepare-started)
          (let [result (source/prepare-init-prefix loaded invoke checked)]
            (vreset! prepared result) (vreset! progress (:world result))
            (vreset! phase :adopt-started)
            (let [next-context (resident/adopt-prepared (packet entry @progress @active) configuration)
                  prefix (InitPrefix.)
                  receipt {:module-count (count (get-in result [:prefix :modules]))
                           :constant-count (count (:constants certificate))
                           :producer-imports (get-in result [:prefix :producer-imports])}]
              (locking issued
                (.put issued prefix {:prefix (:prefix result) :certificate certificate
                                     :configuration configuration :native-bindings native-bindings
                                     :receipt receipt}))
              {:context next-context :prefix prefix :receipt receipt})))
        (catch Throwable cause
          (throw (ex-info (or (.getMessage cause) "Resident Init prefix preparation failed")
                          (merge {:checkpoint @progress :checkpoint-session @active} (ex-data cause)
                                 {:resident-init-prefix-entry entry :resident-init-prefix-checked checked
                                  :resident-init-prefix-preparation @prepared :resident-init-prefix-last-call @last-call
                                  :resident-init-prefix-phase @phase :resident-init-prefix-terminal? true
                                  :resident-init-prefix-root-ownership :inherited-in-independent-branch}) cause)))))))

(defn descriptor
  "Borrow a descriptive receipt; it grants no checking or replay authority."
  [prefix] (:receipt (capability! prefix)))

(defn release-prefix
  "Remove an issued prefix's registry owner in a NEW branch and adopt its roots.
   Public lower release validates exact registry/scaffold/anchor/open Source before
   releasing once. Input and inherited forks retain their registry owner. Closing
   a Context does not release this registry owner or close the borrowed Source."
  [context prefix]
  (locking context
    (let [entry (resident/snapshot context) progress (volatile! (:world entry))
          phase (volatile! :entry) released (volatile! nil)]
      (try
        (let [{raw-prefix :prefix :keys [certificate configuration native-bindings]} (capability! prefix)]
          (preparation-readiness! entry configuration native-bindings)
          (when-not (and (identical? raw-prefix (get-in @progress [:source-import-prefixes (:id (:state raw-prefix))]))
                         (identical? (:env certificate) (:checked-env raw-prefix)))
            (fail "Issued Init prefix is absent or belongs to another branch" {}))
          (vreset! phase :release-started)
          (vreset! progress (source/release-init-prefix @progress raw-prefix))
          (vreset! released (packet entry @progress (:session entry)))
          (vreset! phase :adopt-started)
          {:context (resident/adopt-prepared @released configuration) :receipt (:receipt (capability! prefix))})
        (catch Throwable cause
          (throw (ex-info (or (.getMessage cause) "Resident Init prefix release failed")
                          (merge {:checkpoint @progress :checkpoint-session (:session entry)} (ex-data cause)
                                 {:resident-init-prefix-entry entry :resident-init-prefix-released @released
                                  :resident-init-prefix-phase @phase :resident-init-prefix-terminal? true
                                  :resident-init-prefix-root-ownership :inherited-in-independent-branch}) cause)))))))


;; The staged operation owns its continuation privately. Neither a descriptor nor
;; a copied checkpoint can replace this issued object or restart an effect.
(deftype InitImport [])
(defonce ^:private imports-issued (WeakHashMap.))
(defn- import-control! [control]
  (when-not (instance? InitImport control)
    (fail "Expected an issued resident Init import operation" {}))
  (or (locking imports-issued (.get imports-issued control))
      (fail "Expected an issued resident Init import operation" {})))

(defn- positive-long! [value label]
  (when-not (and (integer? value) (<= 1 value Long/MAX_VALUE))
    (fail "Expected a positive bounded import budget" {:budget label}))
  value)
(defn- import-policy! [policy]
  (when-not (and (map? policy)
                 (every? #{:allow-axioms? :allow-unsafe? :allow-compiler-markers? :fuel} (keys policy)))
    (fail "Init import requires explicit kernel policy; caller projection certificates are forbidden" {}))
  (doseq [key [:allow-axioms? :allow-unsafe? :allow-compiler-markers?] :when (contains? policy key)]
    (when-not (boolean? (get policy key)) (fail "Init import policy flags must be Boolean" {:key key})))
  (when (contains? policy :fuel) (positive-long! (:fuel policy) :checker-fuel))
  policy)
(defn- import-budgets! [budgets]
  (when-not (and (map? budgets) (= #{:outer-fuel :helper-fuel :attempt-fuel} (set (keys budgets))))
    (fail "Init import requires explicit outer/helper/aggregate attempt budgets" {}))
  (doseq [[key value] budgets] (positive-long! value key))
  budgets)
(defn- capture-import-request [request]
  (when-not (and (map? request)
                 (every? #{:path :text :file-name :module-name :roots :initialization} (keys request))
                 (not= (contains? request :path) (contains? request :text))
                 (instance? ansatz.kernel.Name (:module-name request))
                 (vector? (:roots request)) (every? #(instance? ansatz.kernel.Name %) (:roots request))
                 (= :defer (:initialization request)))
    (fail "Init import requires one explicit deferred source request and no calls" {}))
  (let [path (:path request) filename (or (:file-name request) path)]
    (when-not (and (string? filename) (seq filename)
                   (if (contains? request :path) (and (string? path) (seq path)) (string? (:text request))))
      (fail "Init import requires source text/path and file name" {}))
    (-> request (dissoc :path)
        (assoc :text (if (contains? request :path) (slurp path :encoding "UTF-8") (:text request))
               :file-name filename))))

(defn- import-progress [data]
  (cond-> {:phase (:phase data) :guest-steps (:used data 0)
           :outer-steps (:outer-steps data 0) :helper-steps (:helper-steps data 0)
           :completed-operations (:operations data 0)}
    (:reconstruction data) (assoc :reconstruction (get-in data [:reconstruction :audit]))
    (:graph-operation? data) (assoc :source-graph (:graph-audit data))))
(defn- finished-import-state [data]
  ;; The issued token still rejects repeat consumption, but no continuation or
  ;; authority remains usable after successful adoption. Keep only descriptive
  ;; accounting; retaining the old packets here would pin their heap snapshots
  ;; for as long as the caller retains this otherwise exhausted control.
  (cond-> (assoc (select-keys data [:used :outer-steps :helper-steps :operations])
                 :phase :finished :busy? true)
    (:reconstruction data) (assoc :reconstruction {:audit (get-in data [:reconstruction :audit])})
    (:graph-operation? data) (assoc :graph-operation? true :graph-audit (:graph-audit data))))
(defn- import-failure! [state cause]
  ;; Graph proof/check helpers may perform host RC work after their final raw
  ;; getter. Preserve the cause's later exact World/session and paired owners
  ;; in private state as well as the canonical outer exception. Legacy escrow
  ;; fields and behavior stay in their fixed path.
  (when (:graph-operation? @state)
    (let [child (ex-data cause)]
      (when (contains? child :checkpoint) (swap! state assoc :world (:checkpoint child)))
      (when (:checkpoint-session child) (swap! state assoc :session (:checkpoint-session child)))
      (swap! state assoc :graph-child-failure child)))
  (let [data @state previous (:phase data)
        wrapped (ex-info (or (.getMessage cause) "Resident Init import failed")
             (cond-> (merge {:checkpoint (:world data) :checkpoint-session (:session data)} (ex-data cause)
                    {:resident-init-import-entry (:entry data)
                     :resident-init-import-request (:request data)
                     :resident-init-import-header (:header data)
                     :resident-init-import-assembly (:assembly data)
                     :resident-init-import-event (:event data)
                     :resident-init-import-io (:io data)
                     :resident-init-import-finalization (:finished data)
                     :resident-init-import-adoption-entry (:adoption-entry data)
                     :resident-init-import-last-call (:last-call data)
                     :resident-init-import-ownership (:owners data)
                     :resident-init-import-reconstruction (select-keys (:reconstruction data) [:cache :owners :temporary])
                     :resident-init-import-progress (assoc (import-progress data) :phase previous)
                     :resident-init-import-terminal? true})
               (:graph-operation? data) (assoc :source-graph-import-state data :source-graph-import-terminal? true)) cause)]
    (swap! state assoc :phase :failed :failure-phase previous :failure wrapped)
    (throw wrapped)))

(defn prepare-source-import-over-init
  "Parse and assemble ONE published over-Init A requested by captured B text.
   OPTIONS is exactly {:kernel-policy explicit-map :budgets
   {:outer-fuel positive :helper-fuel positive :attempt-fuel positive}}.
   Prefix carries the independent configuration and ORIGINAL checked certificate.
   Header must be pinned classic [Init,meta Init,A], no initializers/calls.
   Return {:control issued-one-shot-operation :progress descriptive-data}.
   No finalizer starts here. Input remains unchanged; new operation owns assembly
   state/imports and encoded Name in its independent branch. Failures are terminal
   exact diagnostic packets, never cleanup/retry or borrowed Source closure."
  [context request prefix {:keys [kernel-policy budgets] :as options}]
  (locking context
    (let [entry (resident/snapshot context)
          state (atom {:entry entry :world (:world entry) :session (:session entry)
                       :phase :entry :used 0 :outer-steps 0 :helper-steps 0 :operations 0
                       :owners {:input-environment :borrowed :input-options :borrowed}})
          invoke (fn [world target args]
                   (swap! state assoc :world world)
                   (let [called (raw/call (:session @state) world target args)]
                     (swap! state assoc :world (:state called) :session (:session called)
                            :last-call {:target target :arguments args :returned called})
                     [(:state called) (:value called)]))]
      (try
        (when-not (and (map? options) (= #{:kernel-policy :budgets} (set (keys options))))
          (fail "Init import requires explicit kernel policy and execution budgets only" {}))
        (import-policy! kernel-policy) (import-budgets! budgets)
        (let [{raw-prefix :prefix :keys [certificate configuration native-bindings]} (capability! prefix)]
          (preparation-readiness! entry configuration native-bindings)
          (standalone/import-readiness! entry configuration)
          (when-not (and (identical? raw-prefix (get-in entry [:world :source-import-prefixes (:id (:state raw-prefix))]))
                         (identical? (:env certificate) (:checked-env raw-prefix)))
            (fail "Issued Init prefix is absent or belongs to another branch" {}))
          (swap! state assoc :prefix raw-prefix :certificate certificate :configuration configuration
                 :native-bindings native-bindings :kernel-policy kernel-policy :budgets budgets
                 :session (assoc (:session entry) :fuel (:helper-fuel budgets))
                 :phase :capture-source)
          (swap! state assoc :request (capture-import-request request) :phase :header-started)
          (let [captured (:request @state)
                parsed (frontend/inspect-file-header (:session @state) (:world @state) (:text captured) (:file-name captured))
                header (:header parsed) requests (:requestedImports header) module (:module (nth requests 2 nil))
                expected (conj source/init-requests {:module module :importAll false :isExported true :isMeta false})]
            (swap! state assoc :header header :world (:world parsed) :session (:session parsed))
            (when-not (and (false? (:hasErrors header)) (false? (:moduleSystem header))
                           (not= source/init-module module) (= expected requests))
              (fail "Init import requires exact classic [Init,meta Init,A] header" {}))
            (let [module-name (reduce name/mk-str (name/anonymous) (str/split (imports/module-string module) #"\."))
                  _ (swap! state assoc :phase :encode-module-started)
                  [world encoded] (encoding/encode-name (:world @state) invoke module-name)]
              (swap! state assoc :world world :module module :module-name encoded :phase :assemble-started)
              (swap! state update :owners assoc :module-name encoded :module-name-state :owned)
              (let [assembled (source/assemble-over-init world invoke raw-prefix module encoded requests)]
                (swap! state assoc :assembly assembled :world (:world assembled))
                (when-not (= :ok (:status assembled))
                  (fail "Init source assembly failed" {:checkpoint (:world assembled) :io-result (:io-result assembled)}))
                (swap! state update :owners assoc :assembly-state (:state assembled) :assembly-imports (:imports assembled)
                       :assembly-owner-state :owned-at-assembly-checkpoint)
                (swap! state assoc :phase :assembled)
                (let [control (InitImport.)]
                  (locking imports-issued (.put imports-issued control state))
                  {:control control :progress (import-progress @state)})))))
        (catch Throwable cause (import-failure! state cause))))))

(declare graph-profile! source-graph-roots)

(defn- continuation-readiness! [{:keys [world session prefix certificate configuration] :as data}]
  ;; Only issued private continuations enter here. Full scaffold/range checks
  ;; remain at existing public assemble/finish use boundaries, not each slice.
  (when-not (and (identical? (:functions world) (:functions session))
                 (identical? prefix (get-in world [:source-import-prefixes (:id (:state prefix))]))
                 (identical? (:env certificate) (:checked-env prefix))
                 (identical? (:source prefix) (first (:native-imports world)))
                 (= 1 (count (:native-imports world))) (false? @(:closed (:source prefix)))
                 (= (:checked-anchor prefix) (get-in world [:kernel-environments (:id (:checked-anchor prefix)) :anchor]))
                 (identical? (:checked-env prefix) (get-in world [:kernel-environments (:id (:checked-anchor prefix)) :env])))
    (fail "Init import continuation no longer matches its prefix/source/anchor" {}))
  (when-not (= (set (keys (:trusted-bindings configuration))) (set (keys (:bindings session))))
    (fail "Init import continuation binding registry changed" {}))
  (doseq [[symbol binding] (:trusted-bindings configuration)]
    (when-not (identical? binding (get-in session [:bindings symbol]))
      (fail "Init import continuation host capability changed" {:symbol symbol})))
  (eval/validate-executables! world (:trusted-functions configuration)
                            (concat preparation-roots standalone/import-roots))
  (when (:graph-operation? data)
    (let [p (graph-profile! (get-in data [:source-graph :profile]))]
      (when-not (and (identical? p (get-in data [:source-graph :profile-data]))
                     (identical? (:token p) (get-in data [:source-graph :profile-token])))
        (fail "Source graph continuation lost its exact issued profile" {}))
      (eval/validate-executables! world (:trusted-functions configuration) source-graph-roots)))
  true)

(declare in-reconstruction-scope release-reconstruction-owners
         graph-invocation finish-source-graph-operation!)

(defn- advance-import-operation!
  "Advance an issued operation in bounded cooperative slices. LIMITS is exactly
   {:max-operations positive :wall-ms positive}, optionally :observe! scalar-fn.
   Wall budget is checked BETWEEN operations, never preempts host/native work.
   Reserve the full next outer/helper bound from the immutable aggregate attempt
   budget before running. Completed events are escrowed before accounting and
   observers; any failure poisons the operation permanently. No caller snapshot,
   budget replacement, retry or finalizer replay is accepted."
  [control {:keys [max-operations wall-ms observe!] :as limits} graph-mode?]
  (let [state (import-control! control)]
    (when-not (= graph-mode? (boolean (:graph-operation? @state)))
      (fail "Import operation belongs to another fixed API" {}))
    (locking control
      (when-let [failure (:failure @state)] (throw failure))
      (when-not (and (not (:busy? @state)) (contains? #{:assembled :running} (:phase @state)))
        (fail "Init import operation is not advanceable" {:phase (:phase @state)}))
      (swap! state assoc :busy? true)
      (try
        (when-not (and (map? limits) (every? #{:max-operations :wall-ms :observe!} (keys limits))
                       (contains? limits :max-operations) (contains? limits :wall-ms)
                       (or (nil? observe!) (fn? observe!)))
          (fail "Init import requires explicit cooperative slice limits" {}))
        (positive-long! max-operations :max-operations) (positive-long! wall-ms :wall-ms)
        (let [started (System/nanoTime)]
          (loop [operations 0]
            (continuation-readiness! @state)
            (let [{:keys [phase assembly world session budgets event used]} @state]
              (if (or (= :io-completed phase) (>= operations max-operations)
                      (>= (/ (- (System/nanoTime) started) 1000000.0) wall-ms))
                {:progress (import-progress @state)}
                (let [boundary? (= :boundary (:status event))
                      bound (get budgets (if boundary? :helper-fuel :outer-fuel))]
                  (when (> bound (- (:attempt-fuel budgets) used))
                    (fail "Init import aggregate budget cannot reserve the next operation" {:reservation bound}))
                  (when (= :assembled phase)
                    ;; Mark before starting: even a start failure is terminal.
                    (swap! state assoc :phase :running :finalizer-started? true)
                    (swap! state assoc :world
                           (m/start world (:finalize source/helpers)
                                    [(:state assembly) (:imports assembly) (get-in @state [:entry :options]) m/erased]))
                    (swap! state update :owners assoc :assembly-owner-state :transferred-to-finalizer))
                  (let [before (:world @state)
                        session (assoc (:session @state) :fuel (:outer-fuel budgets))
                        next-event (in-reconstruction-scope state
                                     #(if boundary?
                                        (raw/complete-host-boundary (:token event) {:helper-fuel (:helper-fuel budgets)})
                                        (raw/advance-to-boundary session before)))]
                    ;; Retain actual result first, including a completed IO even
                    ;; if later budget validation or an observer rejects it.
                    (swap! state assoc :event next-event :world (:state next-event) :session (:session next-event))
                    (when (= :done (:status next-event))
                      (swap! state assoc :io (:value next-event) :phase :io-completed))
                    (let [delta (- (get-in next-event [:state :stats :steps]) (get-in before [:stats :steps]))
                          helper (:helper-steps next-event 0) charge (if boundary? (max delta helper) delta)]
                      (when-not (and (integer? delta) (<= 0 delta bound) (integer? helper) (<= 0 helper bound)
                                     (<= charge (- (:attempt-fuel budgets) used)))
                        (fail "Init import observed an invalid execution-budget charge" {:observed-steps delta :helper-steps helper :bound bound}))
                      (swap! state #(-> % (update :used + charge) (update :operations inc)
                                           (update (if boundary? :helper-steps :outer-steps) + charge)))
                    (when observe! (observe! (import-progress @state)))
                    (recur (inc operations)))))))))
        (catch Throwable cause (import-failure! state cause))
        (finally (swap! state assoc :busy? false))))))

(defn advance-import!
  "Advance an issued operation in bounded cooperative slices. LIMITS is exactly
   {:max-operations positive :wall-ms positive}, optionally :observe! scalar-fn.
   Wall budget is checked BETWEEN operations, never preempts host/native work.
   Reserve the full next outer/helper bound from the immutable aggregate attempt
   budget before running. Completed events are escrowed before accounting and
   observers; any failure poisons the operation permanently. No caller snapshot,
   budget replacement, retry or finalizer replay is accepted."
  [control limits]
  (advance-import-operation! control limits false))

(defn advance-source-graph-import!
  "Advance only an issued completed-only graph operation in bounded slices."
  [control limits]
  (when-not (instance? InitImport control) (fail "Expected an issued graph import operation" {}))
  (advance-import-operation! control limits true))

(defn- finish-import-operation!
  "Fixed legacy/graph finish dispatch. Both paths consume one completed IO,
   validate/check their own exact union, escrow before release/adoption, then
   replace only successful controls with descriptive tombstones."
  [control graph-mode?]
  (let [state (import-control! control)]
    (when-not (= graph-mode? (boolean (:graph-operation? @state)))
      (fail "Import operation belongs to another fixed API" {}))
    (locking control
      (when-let [failure (:failure @state)] (throw failure))
      (when-not (and (not (:busy? @state)) (= :io-completed (:phase @state)))
        (fail "Init import has no unconsumed completed finalizer IO" {:phase (:phase @state)}))
      ;; Claim the IO before any helper/checking effect. Later errors cannot retry.
      (swap! state assoc :phase :checking-started :busy? true)
      (try
        (continuation-readiness! @state)
        (let [{:keys [assembly world io certificate kernel-policy budgets configuration entry]} @state
              invoke (if graph-mode?
                       (graph-invocation state (select-keys budgets [:helper-fuel :attempt-fuel]))
                       (fn [world target args]
                       (swap! state assoc :world world)
                       (let [called (raw/call (assoc (:session @state) :fuel (:helper-fuel budgets)) world target args)]
                         (swap! state assoc :world (:state called) :session (:session called)
                                :last-call {:target target :arguments args :returned called})
                         [(:state called) (:value called)])))
              finished (if graph-mode?
                         (finish-source-graph-operation! state invoke)
                         (source/finish-over-init assembly world io invoke
                           {:kernel-policy (assoc kernel-policy :projection-certificate certificate)}))]
          (swap! state assoc :finished finished :world (:world finished))
          (when-not (= :ok (:status finished))
            (fail "Init source finalizer returned IO error" {:checkpoint (:world finished) :io-result (:io-result finished)}))
          (swap! state update :owners assoc :final-environment (:environment finished)
                 :final-environment-state :owned :assembly-owner-state :consumed-by-successful-finalizer)
          (let [receipt (if graph-mode? (:source-graph-receipts finished) (:source-import-receipt finished))]
            (when-not (if graph-mode?
                        (and (vector? receipt) (= (count receipt) (count (get-in @state [:source-graph :selection :nodes]))))
                        (and receipt (identical? (:checked-env receipt) (get-in finished [:certificate :env]))))
              (fail "Init import has no exact fresh source-only checked receipt" {}))
            (release-reconstruction-owners state)
            (swap! state assoc :phase :adopt-started)
            (when-not graph-mode?
              (swap! state update :world m/release (:module-name @state) 1)
              (swap! state update :owners assoc :module-name-state :released))
            (swap! state update :world m/release (:environment entry) 1)
            (swap! state update :owners assoc :prior-environment-in-new-branch :released)
            (let [prepared (assoc (packet entry (:world @state)
                                               (assoc (:session @state) :fuel (get-in entry [:session :fuel])))
                                 :environment (:environment finished))
                  _ (swap! state assoc :adoption-entry prepared)
                  context (resident/adopt-prepared prepared configuration)
                  _ (when graph-mode? (swap! state assoc :adopted-context context))
                  result (if graph-mode?
                           {:context context :request (:request @state) :header (:header @state)
                            :graph-import-receipts receipt}
                           {:context context :request (:request @state) :header (:header @state)
                            :import-receipt {:module (:module @state) :unit-digest (:unit-digest receipt)
                                             :constant-count (count (:constants receipt))}})
                  completed (finished-import-state @state)
                  result (cond-> result graph-mode? (assoc :progress (import-progress completed)))]
              ;; Construct the complete return value before discarding any
              ;; failure evidence. This changes host reachability only: all
              ;; guest owner releases and the public adoption already succeeded.
              (reset! state completed)
              result)))
        (catch Throwable cause (import-failure! state cause))
        (finally (swap! state assoc :busy? false))))))


(defn finish-import!
  "Consume this operation's completed genuine finalizer IO exactly once. Freshly
   check the WHOLE Init+A map; only immutable native projections may reuse the
   privately retained original certificate. Return new :context, captured :request,
   actual :header and descriptive A-only :import-receipt. No caller certificate,
   finalizer invocation, initializer replay or borrowed lease closure occurs here.
   Successful adoption drops obsolete private continuation packets from this
   exhausted control; returned Context and borrowed input snapshots remain owned
   as before. Failed/unfinished operations retain their exact diagnostic packets."
  [control]
  (finish-import-operation! control false))

(defn finish-source-graph-import!
  "Freshly check a graph union and adopt its atomic completed receipt batch.
   Failed candidate batches remain diagnostic and cannot authorize graph rows."
  [control]
  (when-not (instance? InitImport control) (fail "Expected an issued graph import operation" {}))
  (let [state (import-control! control)]
    (locking control
      (when-not (:graph-operation? @state)
        (fail "Import operation belongs to another fixed API" {}))
      (let [activation (get-in @state [:source-graph :activation])]
        ;; Preserve common terminal-failure/repeat semantics. A successful
        ;; tombstone deliberately no longer retains its activation token.
        (when (and (not (:failure @state)) (not= :finished (:phase @state))
                   (not (and (instance? AtomicBoolean activation)
                             (not (.get ^AtomicBoolean activation)))))
          (fail "Source graph operation has no inactive receipt batch" {}))
        (let [result (finish-import-operation! control true)]
          ;; This is the last effect, AFTER the common function's finally and
          ;; complete result construction. The token has no cap/World backlink.
          (.set ^AtomicBoolean activation true)
          result)))))

;; Pure original-publication provenance groundwork. This does not issue a
;; capability, associate a target, or authorize reconstruction execution.
(defn- proof-array! [world value maximum]
  (let [node (when (m/ref? value) (m/node world value))]
    (when-not (and (= :array (:kind node)) (vector? (:fields node))
                   (<= (count (:fields node)) maximum))
      (fail "Publication proof requires a bounded guest array" {:maximum maximum}))
    (:fields node)))

(defn- publication-proof-with-base!
  [original prefix certificate module invoke {:keys [max-constants name-limits] :as limits} base]
  (let [progress (volatile! (:world original))
        owners (volatile! {})
        call (fn [target args owner]
               (let [[world value] (invoke @progress target args)]
                 (vreset! progress world)
                 (when owner (vswap! owners assoc owner {:value value :state :owned}))
                 value))
        release! (fn [owner]
                   (vreset! progress (m/release @progress (get-in @owners [owner :value]) 1))
                   (vswap! owners assoc-in [owner :state] :released))]
    (try
      (when-not (and (map? limits) (= #{:max-constants :name-limits} (set (keys limits)))
                     (integer? max-constants) (<= 1 max-constants Long/MAX_VALUE))
        (fail "Publication proof requires explicit positive constant/name limits" {}))
      (let [world @progress entry (get-in world [:source-modules module])
            digest (:unit-digest entry) unit (:unit entry)
            environment (:environment original)
            _ (when-not (and (= (:profile base) (:profile entry)) (= module (:module entry))
                             (= environment (:environment entry))
                             (identical? unit (get-in world [:eval-const-authorizations :units digest]))
                             (= [] (:actions unit)) (= [] (get-in unit [:manifest :initializationPlan :actions]))
                             (= module (get-in unit [:manifest :initializationPlan :module]))
                             (= (:imports base) (get-in entry [:metadata :imports]))
                             (= 1 (count (:native-imports world)))
                             (identical? (:source prefix) (first (:native-imports world)))
                             (false? @(:closed (:source prefix))))
                (fail "Original source publication/profile/unit/source mismatch" {}))
            data-node (m/node world (:data entry))
            _ (when-not (and (= 0 (:tag data-node)) (bridge/constructor-layout? data-node 5 1))
                (fail "Original source publication has malformed ModuleData" {}))
            [_ names-ref constants-ref extras-ref _] (:fields data-node)
            names (proof-array! world names-ref max-constants)
            values (proof-array! world constants-ref max-constants)
            extras (proof-array! world extras-ref max-constants)
            _ (when-not (= (count names) (count values))
                (fail "Original source publication name/CI arrays differ" {}))
            exported (reduce (fn [out [name value]]
                               (let [name (bridge/project-name-bounded world name name-limits)]
                                 (when (or (contains? out name) (contains? (:constants base) name)
                                           (not (m/ref? value))
                                           (not= name (imported/project-constant-name world value name-limits)))
                                   (fail "Source publication duplicate, collision or name/ref mismatch" {}))
                                 (assoc out name value))) {} (map vector names values))
            name-refs (into {} (map (fn [value]
                                       [(bridge/project-name-bounded world value name-limits) value])) names)
            seen-extras (volatile! #{})
            guest-names (reduce (fn [out value]
                                  (let [name (bridge/project-name-bounded world value name-limits)]
                                    (when (or (contains? @seen-extras name) (contains? (:constants base) name)
                                              (and (contains? out name) (not (:allow-const-extra? base))))
                                      (fail "Source publication duplicate/colliding constant/extra name" {}))
                                    (vswap! seen-extras conj name)
                                    (assoc out name value))) name-refs extras)
            expected (merge (:constants base) exported)
            _ (when (> (count expected) max-constants)
                (fail "Publication proof exceeds total constant limit" {}))
            root (call (:root imports/helpers) [environment] :root)
            anchored (get-in world [:kernel-environments (:id root)])
            ^Env checked (:env anchored)
            _ (when-not (and (m/ref? root) (= root (:anchor anchored)) (instance? Env checked)
                             (identical? anchored (get-in @progress [:kernel-environments (:id root)])))
                (fail "Original publication has no protected checked anchor" {}))
            constant-map (call (:constant-map imports/helpers) [environment] :constant-map)
            _ (when-not (and (m/ref? constant-map) (= constant-map (:constant-map anchored)))
                (fail "Original publication protected map differs" {}))
            flag (call (:quot-init? imports/helpers) [environment] nil)
            flag (native/nat-value {:ref? m/ref? :node m/node} @progress flag)
            _ (when-not (and (contains? #{0 1} flag)
                             (= (= 1 flag) (:quot-init? anchored) (.isQuotEnabled checked)))
                (fail "Original publication quotient state differs" {}))
            actual-ref (call (:constants imports/helpers) [environment] :constant-array)
            actual (proof-array! @progress actual-ref (count expected))
            _ (when-not (and (= (count actual) (count expected) (count (set actual)))
                             (= (set actual) (set (vals expected)))
                             (= (count expected) (count (.allConstants checked))))
                (fail "Original checked publication is not the exact native plus source CI union" {}))
            _ (doseq [[name ci] (:projected base)]
                (when-not (identical? ci (.lookup checked name))
                  (fail "Original publication changed a native Java ConstantInfo identity" {})))
            projected (into {} (map (fn [[name _]]
                                     (let [ci (.lookup checked name)]
                                       (when-not (and ci (= name (.name ^ConstantInfo ci)))
                                         (fail "Source CI is absent from original checked Java Environment" {}))
                                       [name ci]))) exported)
            proof {:original original :entry entry :unit unit :unit-digest digest :module module
                   :anchor root :constant-map constant-map :checked-env checked :quot-init? (= 1 flag)
                   :constants exported :projected projected :guest-names guest-names :expected expected}]
        ;; These are temporary getter-result owners, not new proof-cache owners.
        ;; The original publication's registry/checked roots remain retained.
        (release! :constant-array) (release! :constant-map) (release! :root)
        (vreset! progress (assoc @progress :result 0))
        {:world @progress :proof proof})
      (catch Throwable cause
        (throw (ex-info (or (.getMessage cause) "Publication provenance proof failed")
                        (merge {:checkpoint @progress} (ex-data cause)
                               {:publication-proof-original original :publication-proof-owners @owners
                                :publication-proof-terminal? true}) cause))))))

(defn- publication-proof!
  ;; Fixed legacy adapter: exact native+ONE source, Init-only publication header,
  ;; and the original no-overlap rule remain unchanged.
  [original prefix certificate module invoke limits]
  (publication-proof-with-base! original prefix certificate module invoke limits
    {:profile :over-init :imports source/init-requests :constants (:constants certificate)
     :projected (:projected certificate) :allow-const-extra? false}))

;; These optional profiles are generation-scoped host capabilities. They are not
;; a hostile-host security boundary: admitted code/bindings obey guest RC and no
;; caller may edit the private continuation's heap. Public candidate worlds are
;; compared with the original checked publication before they enter that scope.
(deftype ReconstructionProfile [])
(deftype ReconstructionPublication [])
(defonce ^:private reconstruction-profiles (WeakHashMap.))
(defonce ^:private reconstruction-publications (WeakHashMap.))
(def ^:private reconstruction-active (ThreadLocal.))
(def ^:private reconstruction-request (ThreadLocal.))
(def reconstruction-helpers
  {:is-exporting ["str" ["str" ["anonymous"] "SourceReconstructionWitness"] "isExporting"]})
;; Fully qualified public getter names (the module-names getter borrows env).
(def ^:private module-names-helper
  ["str" ["str" ["str" ["anonymous"] "Lean"] "Environment"] "allImportedModuleNames"])
(def ^:private module-index-helper
  ["str" ["str" ["str" ["anonymous"] "Lean"] "Environment"] "getModuleIdxFor?"])
(def reconstruction-roots
  (vec (concat (map imports/helpers [:root :constant-map :constants :quot-init?])
               [(:header source/helpers) (:is-exporting reconstruction-helpers)
                module-names-helper module-index-helper])))

(defn- reconstruction-profile! [profile]
  (or (locking reconstruction-profiles (.get reconstruction-profiles profile))
      (fail "Expected an issued reconstruction profile" {})))
(defn- reconstruction-publication! [publication]
  (or (locking reconstruction-publications (.get reconstruction-publications publication))
      (fail "Expected an issued reconstruction publication" {})))

(defn- reconstruction-limits! [limits]
  (when-not (and (map? limits)
                 (= #{:max-constants :name-limits :max-nodes :max-edges :max-bytes
                      :max-units :max-declarations} (set (keys limits))))
    (fail "Reconstruction requires explicit constant, Name, unit/declaration and local-DAG limits" {}))
  (doseq [key [:max-constants :max-nodes :max-edges :max-bytes :max-units :max-declarations]]
    (positive-long! (get limits key) key))
  (when-not (and (map? (:name-limits limits))
                 (= #{:max-nodes :max-chars} (set (keys (:name-limits limits)))))
    (fail "Reconstruction requires explicit Name limits" {}))
  (doseq [[key value] (:name-limits limits)] (positive-long! value key))
  limits)

(def ^:private admission-keys [:units :unit-digests :declarations :functions])

(defn- bounded-admission-scans!
  "Count before traversal. max-declarations bounds the AGGREGATE registry entries
   visited, including both executable maps and existing authority. Unit declaration
   occurrences have their own aggregate check against that same explicit bound."
  [before after {:keys [max-units max-declarations]}]
  (let [maps (concat [(:functions before) (:functions after)]
                     (for [world [before after] key admission-keys]
                       (get-in world [:eval-const-authorizations key])))
        units (map #(get-in % [:eval-const-authorizations :units]) [before after])]
    (when-not (and (every? #(or (nil? %) (map? %)) maps)
                   (<= (reduce + 0 (map count maps)) max-declarations)
                   (<= (reduce + 0 (map count units)) max-units))
      (fail "Reconstruction publication authority exceeds its aggregate bounds" {}))))

(defn- preserve-admission-baseline!
  [before after limits]
  (bounded-admission-scans! before after limits)
  (doseq [[old current] (cons [(:functions before) (:functions after)]
                            (for [key admission-keys]
                              [(get-in before [:eval-const-authorizations key])
                               (get-in after [:eval-const-authorizations key])]))]
    (reduce-kv (fn [_ key value]
                 (when-not (and (contains? current key) (identical? value (get current key)))
                   (fail "Reconstruction publication overwrote baseline authority" {}))
                 nil) nil (or old {})))
  true)

(defn- capture-publication-admission!
  "Capture only the exact successful before->after compilation delta. A module
   may have several evalConst compilation units before its final file-handle unit.
   Same module names or same-shaped rows never substitute for these identities."
  [before after proof limits]
  (preserve-admission-baseline! before after limits)
  (let [old (get-in before [:eval-const-authorizations :units])
        all (get-in after [:eval-const-authorizations :units])
        units (reduce-kv (fn [out digest unit]
                          (if (contains? old digest) out (assoc out digest unit))) {} (or all {}))
        module (:module proof)
        occurrences (reduce-kv (fn [n _ unit]
                                 (when-not (vector? (:declarations unit))
                                   (fail "Reconstruction publication unit declarations are not a vector" {}))
                                 (+ n (count (:declarations unit)))) 0 units)]
    (when-not (and (seq units) (<= occurrences (:max-declarations limits))
                   (identical? (:unit proof) (get units (:unit-digest proof))))
      (fail "Reconstruction publication final handle is outside its bounded unit delta" {}))
    (let [rows
          (reduce-kv
            (fn [rows digest unit]
              (when-not (and (string? digest) (re-matches #"[0-9a-f]{64}" digest)
                             (= module (get-in unit [:manifest :initializationPlan :module]))
                             (= [] (:actions unit))
                             (= [] (get-in unit [:manifest :initializationPlan :actions])))
                (fail "Reconstruction publication has a foreign or initialized compilation unit" {}))
              (reduce
                (fn [rows name]
                  (let [row (get-in after [:eval-const-authorizations :declarations name])
                        function (get-in after [:functions name])]
                    (when-not (and (not (contains? rows name))
                                   (not (contains? (get-in before [:eval-const-authorizations :declarations]) name))
                                   (not (contains? (get-in before [:eval-const-authorizations :unit-digests]) name))
                                   (= name (:name row)) (= module (:sourceModule row)) (true? (:sourceLocal row))
                                   (= digest (get-in after [:eval-const-authorizations :unit-digests name]))
                                   function (identical? function (get-in after [:eval-const-authorizations :functions name])))
                      (fail "Reconstruction publication row/unit/function delta is not exact" {}))
                    (assoc rows name {:digest digest :unit unit :row row :function function})))
                rows (:declarations unit))) {} units)]
      ;; New row provenance cannot hide outside a captured unit's declarations.
      (doseq [key [:declarations :unit-digests]]
        (reduce-kv (fn [_ name _]
                     (when-not (or (contains? (get-in before [:eval-const-authorizations key]) name)
                                    (contains? rows name))
                       (fail "Reconstruction publication has an uncaptured new authority row" {}))
                     nil) nil (get-in after [:eval-const-authorizations key])))
      {:baseline before :units units :rows rows :declaration-count occurrences})))

(defn- publication-admission-matches!
  [world proof limits]
  (let [{:keys [baseline units rows]} (:admission proof)]
    (when-not (and (map? baseline) (seq units) (map? rows))
      (fail "Reconstruction publication has no captured admission delta" {}))
    (preserve-admission-baseline! baseline world limits)
    (doseq [[digest unit] units]
      (when-not (identical? unit (get-in world [:eval-const-authorizations :units digest]))
        (fail "Reconstruction publication unit identity changed" {})))
    (doseq [[name {:keys [digest row function]}] rows]
      (when-not (and (= digest (get-in world [:eval-const-authorizations :unit-digests name]))
                     (identical? row (get-in world [:eval-const-authorizations :declarations name]))
                     (identical? function (get-in world [:functions name]))
                     (identical? function (get-in world [:eval-const-authorizations :functions name])))
        (fail "Reconstruction publication row/unit/function identity changed" {})))
    true))

(defn- local-ci-graph!
  "Bound before expansion/hash/equality. Native leaves belong to the exact closed
   immutable Source; local payload excludes only logical reference counts."
  [world roots {:keys [max-nodes max-edges max-bytes]}]
  (loop [todo (vec roots) nodes {} edges 0 bytes 0]
    (if (empty? todo) nodes
      (let [value (peek todo) todo (pop todo)]
        (if (or (not (m/ref? value)) (contains? nodes (:id value)))
          (recur todo nodes edges bytes)
          (if (m/native-reference? world value)
            (do (when (contains? (:heap world) (:id value))
                  (fail "Reconstruction native CI leaf is shadowed" {}))
                (recur todo nodes edges bytes))
            (let [node (m/node world value) fields (:fields node)
                  _ (when-not (and (contains? #{:ctor :array :string :mpz :byte-array :scalar-array} (:kind node))
                                   (<= (count node) 20)
                                   (every? #{:kind :tag :fields :rc :layout :raw-clone-layout :scalar-bytes
                                             :text :value :integer :bytes :utf8-bytes :values :native-capacity
                                             :native-byte-size :native-utf8-length :element-bytes} (keys node))
                                   (or (nil? (:layout node))
                                       (and (map? (:layout node)) (<= (count (:layout node)) 8)
                                            (every? keyword? (keys (:layout node)))
                                            (every? #(and (integer? %) (<= 0 % Long/MAX_VALUE)) (vals (:layout node)))))
                                   (or (nil? (:scalar-bytes node)) (map? (:scalar-bytes node)) (vector? (:scalar-bytes node)))
                                   (or (nil? (:bytes node)) (vector? (:bytes node)))
                                   (or (nil? (:utf8-bytes node)) (vector? (:utf8-bytes node)))
                                   (or (nil? (:values node)) (vector? (:values node)))
                                   (or (nil? (:integer node)) (integer? (:integer node)))
                                   (or (nil? (:raw-clone-layout node))
                                       (let [layout (:raw-clone-layout node)]
                                         (and (map? layout) (= 3 (count layout))
                                              (= #{:profile :objects :scalar-size} (set (keys layout)))
                                              (= :lean64-align8-v1 (:profile layout))
                                              (integer? (:objects layout)) (<= 0 (:objects layout) 255)
                                              (integer? (:scalar-size layout)) (<= 0 (:scalar-size layout) 1023)
                                              (constructor/physical-layout? node (:objects layout) (:scalar-size layout)))))
                                   (every? #(or (nil? %) (and (integer? %) (<= 0 % Long/MAX_VALUE)))
                                           (map node [:native-capacity :native-byte-size :native-utf8-length :element-bytes]))
                                   (or (nil? (:text node)) (string? (:text node)))
                                   (or (nil? (:value node)) (string? (:value node)) (integer? (:value node)))
                                   (vector? fields))
                      (fail "Reconstruction CI contains an unsupported local payload" {}))
                  edges' (+ edges (count fields))
                  _ (when (or (>= (count nodes) max-nodes) (> edges' max-edges))
                      (fail "Reconstruction original CI DAG exceeds its node/edge bound" {}))
                  _ (when-not (every? #(or (m/ref? %) (instance? prototype.machine.Tag %)
                                           (native/native-scalar? %) (integer? %) (string? %) (= m/erased %)) fields)
                      (fail "Reconstruction CI contains an opaque field" {}))
                  bytes' (+ bytes (count (:scalar-bytes node)) (count (:bytes node))
                            (count (:utf8-bytes node)) (* 8 (count (:values node)))
                            (if (:integer node) (quot (+ 7 (.bitLength (biginteger (:integer node)))) 8) 0)
                            (reduce + 0 (map #(if (integer? %) (quot (+ 7 (.bitLength (biginteger %))) 8) 0) fields))
                            (if (string? (:text node)) (* 2 (count (:text node))) 0)
                            (reduce + 0 (map #(if (string? %) (* 2 (count %)) 0) fields))
                            (if (string? (:value node)) (* 2 (count (:value node))) 0)
                            (if (integer? (:value node)) (quot (+ 7 (.bitLength (biginteger (:value node)))) 8) 0))
                  ]
              (when (> bytes' max-bytes)
                (fail "Reconstruction original CI DAG exceeds its explicit bound" {}))
              (let [byte? (fn [value] (and (integer? value) (<= -128 value 255)))
                    scalar (:scalar-bytes node)]
                (when-not (and (integer? (:tag node)) (<= 0 (:tag node) 250)
                               (integer? (:rc node)) (<= 0 (:rc node) Long/MAX_VALUE)
                               (if (map? scalar)
                                 (every? (fn [[index value]]
                                           (and (integer? index) (<= 0 index Long/MAX_VALUE) (byte? value))) scalar)
                                 (every? byte? scalar))
                               (every? byte? (:bytes node)) (every? byte? (:utf8-bytes node))
                               (every? #(or (instance? Double %) (instance? Float %)) (:values node)))
                  (fail "Reconstruction CI contains an opaque/invalid scalar payload" {})))
              (recur (into todo fields) (assoc nodes (:id value) (dissoc node :rc)) edges' bytes'))))))))

(declare authorize-reconstruction-row)

(defn prepare-reconstruction-profile
  "Create a distinct profile BEFORE independently capturing configuration/prefix.
   HELPER-CONFIGURATION is exactly {:limits {explicit constant/Name/DAG bounds}}.
   Admit reconstruction-roots and the returned exact :eval-binding normally.
   No initializer, checked association or source import receipt is issued."
  [exporter eval-options helper-configuration]
  (when-not (and (map? eval-options) (vector? (:witness eval-options))
                 (map? (:trusted-functions eval-options))
                 (not (contains? eval-options :authorize-source-import)))
    (fail "Reconstruction profile requires its own source authorizer and explicit witness/registry" {}))
  (when-not (and (map? helper-configuration) (= #{:limits} (set (keys helper-configuration))))
    (fail "Reconstruction helper configuration requires only explicit limits" {}))
  (let [limits (reconstruction-limits! (:limits helper-configuration))
        profile (ReconstructionProfile.)
        token (Object.)
        delegate (eval/make-binding exporter
                   (assoc eval-options :authorize-source-import
                     (fn [world context environment row local unit]
                       (if-let [active (.get reconstruction-active)]
                         (authorize-reconstruction-row token active world context environment row local unit)
                         (source/authorize-imported-row world context environment row local unit)))))
        binding (assoc delegate :handler
                  (fn [context world args]
                    (when (.get reconstruction-request)
                      (fail "Reentrant reconstruction evalConst is forbidden" {}))
                    (let [requested (nth args 3)
                          name (bridge/project-name-bounded world requested (:name-limits limits))]
                      (.set reconstruction-request {:name name :reference requested})
                      (try ((:handler delegate) context world args)
                           (finally (.remove reconstruction-request))))))]
    (locking reconstruction-profiles
      (.put reconstruction-profiles profile {:binding binding :limits limits :token token}))
    {:profile profile :eval-binding binding}))

(defn- profile-readiness! [entry prefix profile]
  (let [p (reconstruction-profile! profile) issued (capability! prefix)
        config (:configuration issued)]
    (preparation-readiness! entry config (:native-bindings issued))
    (when-not (and (identical? (:binding p) (get-in config [:trusted-bindings "lean_eval_const"]))
                   (identical? (:binding p) (get-in entry [:session :bindings "lean_eval_const"]))
                   (identical? (:prefix issued)
                               (get-in entry [:world :source-import-prefixes (:id (get-in issued [:prefix :state]))])))
      (fail "Reconstruction requires the exact pre-admitted profile binding and issued prefix" {}))
    (eval/validate-executables! (:world entry) (:trusted-functions config) reconstruction-roots)
    (assoc issued :profile-data p)))

(defn publish-source-for-reconstruction
  "Compile/publish once through resident-source, then privately prove its original
   checked publication. OPTIONS exactly {:proof-budgets {:helper-fuel positive
   :attempt-fuel positive}} bounds ONLY post-publication proof helpers; resident
   compilation/publication retains its independent explicit existing limits.
   Return ordinary publication result with new :reconstruction-publication cap.
   Original result, latest helper session and ownership survive every failure."
  [context request prefix profile {:keys [proof-budgets] :as options}]
  (locking context
    (let [state (atom {:phase :entry :publication nil :used 0})]
      (try
        (when-not (and (= #{:proof-budgets} (set (keys options)))
                       (= #{:helper-fuel :attempt-fuel} (set (keys proof-budgets))))
          (fail "Reconstruction publication requires explicit proof-helper budgets" {}))
        (doseq [[key value] proof-budgets] (positive-long! value key))
        (let [entry (resident/snapshot context)
              {:keys [configuration certificate] raw-prefix :prefix :as issued}
              (profile-readiness! entry prefix profile)
              _ (swap! state assoc :phase :publication-started)
              result (publication/load-and-publish context request
                                                  {:profile :over-init :configuration configuration})
              _ (swap! state assoc :publication result :phase :publication-returned)
              original (resident/snapshot (:context result))
              _ (swap! state assoc :original original :world (:world original) :session (:session original))
              _ (when-not (:success result) (fail "Reconstruction requires a successful source publication" {}))
              invoke (fn [world target args]
                       (swap! state assoc :world world)
                       (let [bound (:helper-fuel proof-budgets)]
                         (when (> bound (- (:attempt-fuel proof-budgets) (:used @state)))
                           (fail "Reconstruction publication cannot reserve next proof helper" {:reservation bound}))
                         (swap! state assoc :reserved bound :phase :proof-helper-started)
                         (try
                           (let [called (raw/call (assoc (:session @state) :fuel bound) world target args)
                                 _ (swap! state assoc :world (:state called) :session (:session called)
                                          :last-call {:target target :arguments args :returned called})
                                 delta (- (get-in called [:state :stats :steps]) (get-in world [:stats :steps]))]
                             (when-not (<= 0 delta bound) (fail "Invalid reconstruction proof helper charge" {}))
                             (swap! state #(-> % (update :used + delta) (assoc :reserved 0 :phase :proof-helper-completed)))
                             [(:state called) (:value called)])
                           (catch Throwable cause
                             (swap! state assoc :world (or (:checkpoint (ex-data cause)) (:world @state))
                                    :session (or (:checkpoint-session (ex-data cause)) (:session @state))
                                    :phase :proof-helper-failed :proof-helper-budget-poisoned? true
                                    :failed-helper {:target target :arguments args :cause cause})
                             (throw cause)))))
              limits (get-in issued [:profile-data :limits])
              proved (publication-proof! original raw-prefix certificate
                                         (get-in result [:publication :module]) invoke
                                         (select-keys limits [:max-constants :name-limits]))
              _ (swap! state assoc :world (:world proved) :phase :proof-completed)
              proof (assoc (:proof proved) :admission
                           (capture-publication-admission! (:world entry) (:world original) (:proof proved) limits))
              graph (local-ci-graph! (:world original) (vals (:constants proof)) limits)
              next-packet (assoc original :world (:world proved)
                                :session (assoc (:session @state) :fuel (get-in original [:session :fuel])))
              _ (swap! state assoc :adoption-entry next-packet :phase :adopt-started)
              next-context (resident/adopt-prepared next-packet configuration)
              cap (ReconstructionPublication.)]
          (locking reconstruction-publications
            (.put reconstruction-publications cap
              {:profile profile :prefix prefix :proof proof :graph graph :original-result result}))
          (assoc result :context next-context :reconstruction-publication cap))
        (catch Throwable cause
          (throw (ex-info (or (.getMessage cause) "Reconstruction publication failed")
                          (merge {:checkpoint (:world @state) :checkpoint-session (:session @state)}
                                 (ex-data cause) {:reconstruction-publication-state @state
                                                 :reconstruction-publication-terminal? true}) cause)))))))

(defn prepare-source-reconstruction-import-over-init
  "Authenticate exact publication/profile and bounded original CI payloads before
   the existing one-shot assembly. OPTIONS retains existing staged import budgets;
   preparation uses existing independent per-helper limits (no global claim).
   Reconstruction is armed only within later authenticated raw driver operations."
  [context request prefix profile publication options]
  (locking context
    (let [entry (resident/snapshot context)
          issued (profile-readiness! entry prefix profile)
          published (reconstruction-publication! publication)
          proof (:proof published) world (:world entry)
          module (:module proof)]
      (when-not (and (identical? profile (:profile published)) (identical? prefix (:prefix published))
                     (identical? (:entry proof) (get-in world [:source-modules module]))
                     (identical? (:unit proof) (get-in world [:eval-const-authorizations :units (:unit-digest proof)]))
                     (identical? (:source (:prefix issued)) (first (:native-imports world)))
                     (identical? (get-in proof [:original :world :kernel-environments (:id (:anchor proof))])
                                 (get-in world [:kernel-environments (:id (:anchor proof))]))
                     (publication-admission-matches! world proof (get-in issued [:profile-data :limits]))
                     (= (:graph published)
                        (local-ci-graph! world (vals (:constants proof)) (get-in issued [:profile-data :limits]))))
        (fail "Reconstruction candidate differs from its exact original checked publication" {}))
      (let [{:keys [control] :as result} (prepare-source-import-over-init context request prefix options)
            state (import-control! control)]
        (try
          (when-not (= module (:module @state))
            (fail "Reconstruction import requests another source module" {}))
          (swap! state assoc :reconstruction {:profile profile :publication publication :proof proof
                                             :limits (get-in issued [:profile-data :limits])
                                             :assembly (:assembly @state) :cache nil :owners {}
                                             :audit {:authorization-count 0 :requested-names [] :names-truncated? false
                                                     :module module :unit-digest (:unit-digest proof)}})
          (assoc result :progress (import-progress @state))
          (catch Throwable cause (import-failure! state cause)))))))

(defn- in-reconstruction-scope [state action]
  (when (.get reconstruction-active) (fail "Reentrant reconstruction driver is forbidden" {}))
  (if-not (:reconstruction @state) (action)
    (do
      (when (.get reconstruction-active) (fail "Reentrant reconstruction driver is forbidden" {}))
      (.set reconstruction-active {:state state :thread (Thread/currentThread)})
      (try (action) (finally (.remove reconstruction-active))))))

(defn- release-reconstruction-owners [state]
  (doseq [[owner {:keys [value status]}] (get-in @state [:reconstruction :owners])
          :when (= :owned status)]
    (swap! state update :world m/release value 1)
    (swap! state assoc-in [:reconstruction :owners owner :status] :released))
  nil)

(defn- structured-name-value [^ansatz.kernel.Name value]
  (loop [value value parts []]
    (if (.isAnonymous value)
      (reduce (fn [prefix [kind payload]] [kind prefix payload]) ["anonymous"] (rseq parts))
      (recur (.prefix value) (conj parts (if (.isStr value) ["str" (.str value)]
                                            ["num" (str (.num value))]))))))

(defn- bounded-name-display
  "Descriptive only; never recurse/allocate a whole over-limit Name display."
  [^ansatz.kernel.Name value]
  (loop [value value parts [] characters 0]
    (if (.isAnonymous value)
      (if (empty? parts) "[anonymous]" (str/join "." (rseq parts)))
      (when (< (count parts) 4096)
        (let [part (if (.isStr value) (.str value) (str (.num value)))
              characters (+ characters (count part) (if (seq parts) 1 0))]
          (when (<= characters 4096)
            (recur (.prefix value) (conj parts part) characters)))))))

(defn- bounded-row-display [value]
  (loop [value value parts [] characters 0]
    (cond
      (= ["anonymous"] value) (if (seq parts) (str/join "." (rseq parts)) "[anonymous]")
      (or (>= (count parts) 4096) (not (vector? value)) (not= 3 (count value))
          (not (contains? #{"str" "num"} (first value))) (not (string? (nth value 2)))) nil
      :else (let [part (nth value 2) characters (+ characters (count part) (if (seq parts) 1 0))]
              (when (<= characters 4096)
                (recur (second value) (conj parts part) characters))))))

(defn- authorize-reconstruction-row [token active world context environment row local unit]
  (let [state (:state active) data @state recon (:reconstruction data)
        proof (:proof recon) requested (.get reconstruction-request)
        captured (get-in proof [:admission :rows (:name row)])
        limits (:limits recon) checkpoint! (:checkpoint! context)
        progress (volatile! world)
        temporary (volatile! {})
        save! (fn [world]
                (vreset! progress world)
                (when checkpoint! (checkpoint! world))
                world)
        call! (fn [target args owner]
                (let [[world value] ((:invoke context) @progress target args)]
                  (vreset! progress world)
                  (when owner
                    (vswap! temporary assoc owner {:value value :status :owned})
                    (swap! state assoc-in [:reconstruction :temporary] @temporary))
                  (save! world)
                  value))
        release! (fn [owner]
                   (vreset! progress (m/release @progress (get-in @temporary [owner :value]) 1))
                   (vswap! temporary assoc-in [owner :status] :released)
                   (swap! state assoc-in [:reconstruction :temporary] @temporary)
                   (save! @progress))]
    (let [predicates
          {:profile-token? (identical? token (:token (reconstruction-profile! (:profile recon))))
           :active-thread? (identical? (:thread active) (Thread/currentThread))
           :running? (= :running (:phase data)) :busy? (true? (:busy? data))
           :no-proof-reentry? (not (:proof-in-progress? recon))
           :same-assembly? (identical? (:assembly recon) (:assembly data))
           :requested? (some? requested) :checkpoint? (fn? checkpoint!)
           :trusted-function-check? (fn? (:check-trusted-functions! context))
           :same-publication? (identical? (:entry proof) (get-in world [:source-modules (:module proof)]))
           :captured-row? (some? captured)
           :same-row-unit? (and (some? captured) (identical? unit (:unit captured)))
           :same-current-unit? (and (some? captured)
                                    (identical? unit (get-in world [:eval-const-authorizations :units (:digest captured)])))
           :same-row-digest? (and (some? captured)
                                  (= (:digest captured) (get-in world [:eval-const-authorizations :unit-digests (:name row)])))
           :same-local-row? (and (some? captured) (identical? local (:row captured)))
           :same-source-module? (= (:module proof) (:sourceModule row))
           :imported-row? (false? (:sourceLocal row))
           :exported-primary-ci? (contains? (:constants proof) (:name requested))}]
      (when-not (every? true? (vals predicates))
        (fail "Source reconstruction callback is outside its exact active publication/primary CI"
              {:reconstruction-guard
               {:predicates predicates :row-name (bounded-row-display (:name row))
                :requested-name (when requested (bounded-name-display (:name requested)))
                :publication-unit-digest (:unit-digest proof) :captured-row-unit-digest (:digest captured)
                :current-row-unit-digest (let [digest (get-in world [:eval-const-authorizations :unit-digests (:name row)])]
                                           (when (and (string? digest) (<= (count digest) 64)) digest))}})))
    (swap! state assoc-in [:reconstruction :proof-in-progress?] true)
    (try
      ((:check-trusted-functions! context) world reconstruction-roots)
      (publication-admission-matches! world proof limits)
      (let [root (call! (:root imports/helpers) [environment] :root)
            constant-map (call! (:constant-map imports/helpers) [environment] :map)
            flag (call! (:quot-init? imports/helpers) [environment] nil)
            _ (when-not (and (m/ref? root) (m/ref? constant-map)
                             (= (if (:quot-init? proof) 1 0)
                                (native/nat-value {:ref? m/ref? :node m/node} @progress flag)))
                (fail "Source reconstruction target root/map/quotient differs" {}))
            visibility (call! (:is-exporting reconstruction-helpers) [environment] nil)
            _ (when-not (= 0 (native/nat-value {:ref? m/ref? :node m/node} @progress visibility))
                (fail "Source reconstruction requires the actual private selected view" {}))
            text (call! (:header source/helpers) [environment] :header)
            header (json/read-str (string/string-value {:ref? m/ref? :node m/node} @progress text) :key-fn keyword)
            _ (when-not (and (= "lean-source-import-header/1" (:schema header))
                             (= "SourceModuleImport.finalizerHeader" (:producer header))
                             (= (get prim/pinned-build "lean_get_githash") (:leanCommit header))
                             (false? (:moduleSystem header))
                             (= (get-in data [:header :requestedImports]) (:imports header)))
                (fail "Source reconstruction target header differs from authenticated assembly" {}))
            _ (release! :header)
            names-ref (call! module-names-helper [environment] :module-names)
            names (mapv #(structured-name-value (bridge/project-name-bounded @progress % (:name-limits limits)))
                        (proof-array! @progress names-ref (:max-constants limits)))
            expected-names (conj (mapv :module (:modules (:prefix data))) (:module proof))
            _ (when-not (= expected-names names)
                (fail "Source reconstruction target module order differs" {}))
            _ (release! :module-names)
            name-ref (some (fn [[name reference]]
                             (when (= (:name row) (structured-name-value name)) reference)) (:guest-names proof))
            _ (when-not name-ref
                (fail "Source reconstruction row lacks an exported/IR-extra module name" {}))
            index (call! module-index-helper [environment name-ref] :index)
            index-node (when (m/ref? index) (m/node @progress index))
            _ (when-not (and (= 1 (:tag index-node)) (bridge/constructor-layout? index-node 1 0)
                             (= (dec (count expected-names))
                                (native/nat-value {:ref? m/ref? :node m/node} @progress (first (:fields index-node)))))
                (fail "Source reconstruction row belongs to another selected module" {}))
            _ (release! :index)
            cache (:cache (:reconstruction @state))]
        (when-not (or (nil? cache) (= constant-map (:map cache)))
          (fail "Source reconstruction protected target map changed within its attempt" {}))
        (when-not cache
          (let [values-ref (call! (:constants imports/helpers) [environment] :constants)
                expected (:expected proof)
                values (proof-array! @progress values-ref (:max-constants limits))]
            (when-not (and (= (count values) (count expected) (count (set values)))
                           (= (set values) (set (vals expected))))
              (fail "Source reconstruction target is not the exact original native plus source CI map" {}))
            (release! :constants)
            ;; Turn the getter owners into explicit proof-cache owners. No
            ;; additional retain is necessary: these are genuine owned results.
            (doseq [[owner value] [[:root root] [:map constant-map]]]
              (swap! state assoc-in [:reconstruction :owners owner] {:value value :status :owned})
              (vswap! temporary assoc-in [owner :status] :transferred-to-cache)
              (swap! state assoc-in [:reconstruction :temporary] @temporary)
              (save! @progress))
            (swap! state assoc-in [:reconstruction :cache]
                   {:map constant-map :root root :header header :modules names :quot-init? (:quot-init? proof)})))
        (when cache (release! :map) (release! :root))
        ;; Descriptive audit is bounded and grants no permission. Existing
        ;; progress observers see it only after the raw scope has been removed.
        (let [display (bounded-name-display (:name requested))]
          (swap! state update-in [:reconstruction :audit]
                 (fn [audit]
                   (let [audit (update audit :authorization-count inc)
                         names (:requested-names audit)]
                     (cond
                       (and display (some #{display} names)) audit
                       (and display (< (count names) 64))
                       (update audit :requested-names conj display)
                       :else (assoc audit :names-truncated? true))))))
        [@progress true])
      (catch Throwable cause
        (throw (ex-info (or (.getMessage cause) "Source reconstruction proof failed")
                        (merge {:checkpoint @progress} (ex-data cause)
                               {:reconstruction-proof-owners (get-in @state [:reconstruction :owners])
                                :reconstruction-proof-temporary @temporary}) cause)))
      (finally (swap! state assoc-in [:reconstruction :proof-in-progress?] false)))))

;; Ordinary source graphs have separate issued identities and completed-only
;; authorization. They never enter reconstruction-active/request scope.
(deftype SourceGraphProfile [])
(deftype SourceGraphNode [])
(deftype SourceGraphReceipt [])
(defonce ^:private graph-profiles (WeakHashMap.))
(defonce ^:private graph-nodes (WeakHashMap.))
(defonce ^:private graph-receipts (WeakHashMap.))
(def graph-assemble-helper
  ["str" ["str" ["anonymous"] "SourceModuleGraphImport"] "assembleClassicGraphOverInit"])
(def source-graph-roots
  (vec (distinct (concat preparation-roots standalone/import-roots
                         publication/publication-roots reconstruction-roots
                         [graph-assemble-helper]))))
(def ^:private graph-limit-keys
  #{:max-modules :max-roots :max-edges :max-depth :max-names :max-name-nodes
    :max-name-bytes :max-total-name-bytes :max-key-bytes :max-total-key-bytes})
(declare authorize-completed-graph-row graph-json!)

(defn- graph-utf8-size!
  "Count valid Unicode without allocating an encoded byte array."
  [^String text budget]
  (loop [index 0 bytes 0]
    (if (= index (.length text)) bytes
      (let [c (.charAt text index)
            pair? (Character/isHighSurrogate c)
            _ (when (or (Character/isLowSurrogate c)
                        (and pair? (or (= (inc index) (.length text))
                                       (not (Character/isLowSurrogate (.charAt text (inc index)))))))
                (fail "Source graph Name has an invalid Unicode scalar" {}))
            size (cond pair? 4 (< (int c) 128) 1 (< (int c) 2048) 2 :else 3)
            next-bytes (+' bytes size)]
        (when (> next-bytes budget) (fail "Source graph Name exceeds byte bound" {}))
        (recur (+ index (if pair? 2 1)) next-bytes)))))

(defn- graph-wire-name!
  "Bound before hashing/rendering. String counts gate Unicode scans; UTF-8 bytes
   and the helper's ten-byte numeric charge use the SAME explicit byte budget.
   Numeric payloads remain decimal strings until the UInt32 cap is established."
  ([encoded module? limits] (graph-wire-name! encoded module? limits nil))
  ([encoded module? limits total-bytes]
   (let [budget (min (:max-name-bytes limits)
                     (if total-bytes (- (:max-total-name-bytes limits) @total-bytes)
                         (:max-name-bytes limits)))]
    (loop [current encoded nodes 0 bytes 0]
     (when (> (inc nodes) (:max-name-nodes limits))
       (fail "Source graph Name exceeds spine bound" {}))
     (if (and (vector? current) (= 1 (count current)) (= "anonymous" (first current)))
       (do (when (and module? (zero? nodes)) (fail "Anonymous source graph module" {}))
           (when total-bytes (vswap! total-bytes +' bytes)) encoded)
       (do
         (when-not (and (vector? current) (= 3 (count current)))
           (fail "Source graph requires a structured Name" {}))
         (let [[tag parent part] current string-node? (= "str" tag)]
           (when-not (and (or string-node? (= "num" tag)) (string? part)
                          (<= (count part) (- budget bytes)))
             (fail "Source graph Name payload exceeds bound" {}))
           (let [size (if string-node? (graph-utf8-size! part (- budget bytes)) 10)
                 total (+' bytes size)]
             (when (> total budget) (fail "Source graph Name exceeds byte bound" {}))
             (when (and module? (or (not string-node?) (empty? part) (.contains ^String part ".")))
               (fail "Source graph module requires roundtrip string segments" {}))
             (when (and (not string-node?)
                        (not (and (<= 1 (count part) 10) (re-matches #"(?:0|[1-9][0-9]*)" part)
                                  (or (< (count part) 10) (not (pos? (compare part "4294967295")))))))
               (fail "Source graph numeric Name exceeds UInt32 profile" {}))
             (recur parent (inc nodes) total)))))))))

(defn- graph-java-name!
  "Bound the caller's Java Name before allocating its wire representation."
  [value module? limits]
  (when-not (instance? ansatz.kernel.Name value)
    (fail "Source graph requires a kernel Name" {}))
  (loop [^ansatz.kernel.Name current value parts [] bytes 0]
    (when (> (inc (count parts)) (:max-name-nodes limits))
      (fail "Source graph Name exceeds spine bound" {}))
    (if (.isAnonymous current)
      (do (when (and module? (empty? parts)) (fail "Anonymous source graph module" {}))
          (reduce (fn [prefix [kind payload]] [kind prefix payload]) ["anonymous"] (rseq parts)))
      (let [remaining (- (:max-name-bytes limits) bytes)
            string? (.isStr current)
            part (if string? (.str current) (.num current))
            size (if string?
                   (do (when (> (count part) remaining) (fail "Source graph Name exceeds byte bound" {}))
                       (graph-utf8-size! part remaining))
                   (do (when-not (and (.isNum current) (<= 0 part 4294967295) (>= remaining 10))
                         (fail "Source graph numeric Name exceeds UInt32 profile" {})) 10))]
        (when (and module? (or (not string?) (empty? part) (.contains ^String part ".")))
          (fail "Source graph module requires roundtrip string segments" {}))
        (recur (.prefix current) (conj parts [(if string? "str" "num") (if string? part (str part))])
               (+' bytes size))))))

(defn- bounded-header-json!
  "Gate bytes and lexical nesting before the JSON parser's recursive descent.
   This is a bounded parser input check, never an authority or identity digest."
  [text maximum depth-limit]
  (do
    (when-not (and (string? text) (<= (count text) maximum))
      (fail "Bounded JSON exceeds parsing bound" {}))
    (graph-utf8-size! text maximum)
    (loop [index 0 depth 0 quoted? false escaped? false]
      (when (< index (count text))
        (let [c (.charAt ^String text index)]
          (cond
            escaped? (recur (inc index) depth quoted? false)
            (and quoted? (= c \\)) (recur (inc index) depth true true)
            (= c \") (recur (inc index) depth (not quoted?) false)
            quoted? (recur (inc index) depth true false)
            (or (= c \[) (= c \{))
            (do (when (>= depth depth-limit) (fail "Bounded JSON exceeds nesting bound" {}))
                (recur (inc index) (inc depth) false false))
            (or (= c \]) (= c \}))
            (do (when (zero? depth) (fail "Bounded JSON has unmatched delimiters" {}))
                (recur (inc index) (dec depth) false false))
            :else (recur (inc index) depth false false)))))
    (json/read-str text :key-fn keyword)))

(defn- graph-json! [text limits graph-limits]
  (bounded-header-json! text (:max-bytes limits) (+' 32 (:max-name-nodes graph-limits))))

(defn- graph-profile! [profile]
  (or (when (instance? SourceGraphProfile profile)
        (locking graph-profiles (.get graph-profiles profile)))
      (fail "Expected an issued source graph profile" {})))
(defn- graph-node! [node]
  (or (when (instance? SourceGraphNode node) (locking graph-nodes (.get graph-nodes node)))
      (fail "Expected an issued source graph node" {})))
(defn- graph-receipt! [receipt]
  (or (when (instance? SourceGraphReceipt receipt)
        (let [data (locking graph-receipts (.get graph-receipts receipt))
              activation (:activation data)]
          (when (and (instance? AtomicBoolean activation) (.get ^AtomicBoolean activation)) data)))
      (fail "Expected an issued completed source graph receipt" {})))

(defn prepare-source-graph-profile
  "Issue a distinct completed-only graph binding BEFORE configuration/prefix
   capture. Configuration is exactly {:limits explicit-CI/admission/DAG-limits
   :graph-limits explicit-module/edge/Name-byte/key-limits
   :host-limits {:max-heap-entries explicit-shadow-scan-bound}}. No initializer,
   checked association, publication or before-completion permission is issued.
   Return :profile, :eval-binding and fixed :install-options. Capture the latter
   in configuration :frontend-configuration before prefix preparation; file
   witnesses use the same selected witness/format as evalConst."
  [exporter eval-options helper-configuration]
  (when-not (and (map? eval-options) (vector? (:witness eval-options))
                 (map? (:trusted-functions eval-options))
                 (not (contains? eval-options :authorize-source-import))
                 (map? helper-configuration)
                 (= 3 (count helper-configuration))
                 (= #{:limits :graph-limits :host-limits} (set (keys helper-configuration))))
    (fail "Source graph profile requires its own authorizer and explicit limits" {}))
  ;; Bound key inventories before the legacy fixed-limit validator traverses
  ;; them. Legacy callers keep their original validation behavior.
  (when-not (and (map? (:limits helper-configuration)) (= 7 (count (:limits helper-configuration)))
                 (map? (get-in helper-configuration [:limits :name-limits]))
                 (= 2 (count (get-in helper-configuration [:limits :name-limits]))))
    (fail "Source graph profile requires bounded fixed CI/Name limit keys" {}))
  (let [limits (reconstruction-limits! (:limits helper-configuration))
        graph-limits (:graph-limits helper-configuration)
        host-limits (:host-limits helper-configuration)
        _ (when-not (and (map? host-limits) (= 1 (count host-limits))
                          (contains? host-limits :max-heap-entries))
            (fail "Source graph profile requires an explicit host heap scan bound" {}))
        _ (positive-long! (:max-heap-entries host-limits) :max-heap-entries)
        _ (when-not (and (map? graph-limits) (= (count graph-limit-keys) (count graph-limits))
                          (= graph-limit-keys (set (keys graph-limits))))
            (fail "Source graph profile requires exact assembly limits" {}))
        _ (doseq [[key value] graph-limits] (positive-long! value key))
        profile (SourceGraphProfile.) token (Object.)
        authorizer (fn [world context environment row local unit]
                     (authorize-completed-graph-row token limits graph-limits
                                                   world context environment row local unit))
        binding (eval/make-binding exporter (assoc eval-options :authorize-source-import authorizer))
        ;; Both consumers use invoke-witness with the same Env/Name/IO args and
        ;; selected format, including the shared typed-IR witness. Keep the
        ;; admitted lower-extern policy; file installation always defers init.
        install-options (assoc eval-options :authorize-source-import authorizer :initialize? false)]
    ;; A separate token avoids a strong value -> closure -> weak-key cycle.
    (locking graph-profiles
      (.put graph-profiles profile {:token token :binding binding :authorizer authorizer
                                   :installer-witness (:witness eval-options)
                                   :installer-witness-format (get eval-options :witness-format :json-string)
                                   :limits limits :graph-limits graph-limits :host-limits host-limits}))
    {:profile profile :eval-binding binding :install-options install-options}))

(defn- graph-installer-matches! [profile configuration]
  (let [options (get-in configuration [:frontend-configuration :install-options])]
    ;; This is closure/witness identity plus fixed semantics, NOT map identity:
    ;; a captured lower-extern policy may coexist with the fixed graph route.
    (when-not (and (map? options)
                   (identical? (:authorizer profile) (:authorize-source-import options))
                   (identical? (:installer-witness profile) (:witness options))
                   (= (:installer-witness-format profile) (get options :witness-format :json-string))
                   (not (:initialize? options)))
      (fail "Source graph requires its exact completed installer and witness" {}))
    true))

(defn- graph-readiness! [entry prefix profile]
  (let [p (graph-profile! profile)
        _ (when-not (instance? InitPrefix prefix) (fail "Expected an issued graph Init prefix" {}))
        issued (capability! prefix)
        configuration (:configuration issued)]
    (graph-installer-matches! p configuration)
    (preparation-readiness! entry configuration (:native-bindings issued))
    (when-not (and (identical? (:binding p) (get-in configuration [:trusted-bindings "lean_eval_const"]))
                   (identical? (:binding p) (get-in entry [:session :bindings "lean_eval_const"]))
                   (identical? (:prefix issued)
                               (get-in entry [:world :source-import-prefixes
                                              (:id (get-in issued [:prefix :state]))])))
      (fail "Source graph requires its exact pre-admitted binding and issued prefix" {}))
    ;; The existing prefix validator scans for native-range shadows. Bound its
    ;; whole-heap work before entering that unchanged legacy validator too.
    (when (> (count (get-in entry [:world :heap])) (get-in p [:host-limits :max-heap-entries]))
      (fail "Source graph heap exceeds explicit prefix-validation bound" {}))
    (source/validate-init-prefix! (:world entry) (:prefix issued))
    (eval/validate-executables! (:world entry) (:trusted-functions configuration) source-graph-roots)
    (assoc issued :graph-profile p)))

(defn- graph-source-matches!
  "Exact open Source and bounded no-shadow proof. Optional evidence belongs only
   to this operation and is reusable only for an identical immutable heap/Source."
  [world node evidence]
  (let [source (:source node) sources (:native-imports world) heap (:heap world)
        maximum (get-in node [:host-limits :max-heap-entries])]
    (when-not (and source (= 1 (count sources)) (identical? source (first sources))
                   (false? @(:closed source)))
      (fail "Source graph publication Native Source changed or closed" {}))
    (when-not (and (integer? maximum) (pos? maximum) (<= (count heap) maximum))
      (fail "Source graph heap exceeds explicit shadow-scan bound" {}))
    (let [prior (when evidence @evidence)
          immutable? (instance? clojure.lang.IPersistentMap heap)]
      (when-not (and immutable? prior (identical? heap (:heap prior))
                     (identical? source (:source prior)))
        (let [start (:base source) end (+' start (:size source))]
          (when (some #(and (integer? %) (<= start %) (< % end)) (keys heap))
            (fail "Source graph immutable Native Source range is shadowed" {})))
        (when (and evidence immutable?)
          (vreset! evidence {:heap heap :source source}))))
    true))

(defn- graph-entry-matches!
  "Receipt updates may extend the original entry, but never replace provenance.
   Compare original values by identity before accepting a candidate world."
  ([world node] (graph-entry-matches! world node true))
  ([world node full-admission?] (graph-entry-matches! world node full-admission? nil))
  ([world node full-admission? source-evidence]
   (graph-source-matches! world node source-evidence)
   (let [original (:entry node) current (get-in world [:source-modules (:module node)])
        allowed (conj (set (keys original)) :graph-import)]
    (when-not (and (map? current)
                   (<= (count current) (count allowed))
                   (every? #(contains? allowed %) (keys current))
                   (every? (fn [[key value]] (identical? value (get current key))) original)
                   (or (not full-admission?)
                       (publication-admission-matches! world (:proof node) (:limits node)))
                   (= (:data-graph node)
                      (local-ci-graph! world [(:data original)] (:limits node))))
      (fail "Source graph candidate differs from its sealed publication" {}))
     current)))

(defn- completed-graph-candidates [token world entry row local unit]
  (let [receipt (:graph-import entry)]
    (reduce
      (fn [out receipt]
        ;; Reject descriptive maps before WeakHashMap hashing or guest work.
        (if-not (instance? SourceGraphReceipt receipt) out
          (let [r (locking graph-receipts (.get graph-receipts receipt))
                node (when (instance? SourceGraphNode (:node r))
                       (locking graph-nodes (.get graph-nodes (:node r))))
                captured (get-in node [:proof :admission :rows (:name row)])
                anchor (get-in world [:kernel-environments (:id (:anchor r))])]
            (if (and r node (instance? AtomicBoolean (:activation r))
                     (.get ^AtomicBoolean (:activation r))
                     (identical? token (:profile-token r))
                     (identical? token (:profile-token node))
                     (= (:module node) (:sourceModule row) (:module r))
                     captured (false? (:sourceLocal row))
                     (identical? unit (:unit captured))
                     (identical? unit (get-in world [:eval-const-authorizations :units (:digest captured)]))
                     (= (:digest captured) (get-in world [:eval-const-authorizations :unit-digests (:name row)]))
                     (identical? local (:row captured))
                     (identical? local (get-in world [:eval-const-authorizations :declarations (:name row)]))
                     (identical? (:function captured) (get-in world [:functions (:name row)]))
                     (identical? (:function captured)
                                 (get-in world [:eval-const-authorizations :functions (:name row)]))
                     (= (:anchor r) (:anchor anchor)) (= (:constant-map r) (:constant-map anchor))
                     (identical? (:checked-env r) (:env anchor)))
              (conj out [r node]) out)))) [] (if receipt [receipt] []))))

(defn- authorize-completed-graph-row
  [token limits graph-limits world context environment row local unit]
  ;; Names are bounded before source-registry/captured-row lookups hash them.
  (graph-wire-name! (:sourceModule row) true graph-limits)
  (graph-wire-name! (:name row) false graph-limits)
  (let [entry (get-in world [:source-modules (:sourceModule row)])]
    (if-not (= :graph (:profile entry))
      (source/authorize-imported-row world context environment row local unit)
      (let [candidates (completed-graph-candidates token world entry row local unit)]
        (if (empty? candidates) [world false]
          (let [progress (volatile! world) owners (volatile! {}) checkpoint! (:checkpoint! context)
                invoke (:invoke context) checker (:check-trusted-functions! context)
                save! (fn [world]
                        (vreset! progress world)
                        (when checkpoint! (checkpoint! world))
                        world)
                call! (fn [target args owner]
                        (let [[world value] (invoke @progress target args)]
                          (vreset! progress world)
                          (when owner (vswap! owners assoc owner {:value value :status :owned}))
                          (save! world)
                          value))
                release! (fn [owner]
                           (vreset! progress (m/release @progress (get-in @owners [owner :value]) 1))
                           (vswap! owners assoc-in [owner :status] :released)
                           (save! @progress))]
            (try
              (when-not (and (fn? invoke) (fn? checker) (fn? checkpoint!))
                (fail "Completed graph authorization requires authenticated raw helper context" {}))
              (checker world reconstruction-roots)
              ;; Only the requested captured row is checked here; full baseline
              ;; admission preservation belongs to sealed operation preparation.
              ;; Protected map/registry owners prevent lawful unique RC reuse.
              (doseq [[_ node] candidates] (graph-entry-matches! @progress node false))
              (let [inherit-context
                    (assoc context :invoke
                      (fn [_ target args]
                        (let [owner (cond (= target (:root imports/helpers)) :inherit-root
                                          (= target (:constant-map imports/helpers)) :inherit-map)
                              value (call! target args owner)]
                          [@progress value])))
                    before @progress
                    [world ^Env checked] (kernel-host/inherit-checked-association
                                          inherit-context before environment imports/helpers)
                    root (get-in @owners [:inherit-root :value])]
                (vreset! progress world)
                ;; inherit-checked-association consumes its getter owners; a new
                ;; header-only anchor transfers the root owner to the world.
                (when root
                  (vswap! owners assoc-in [:inherit-root :status]
                          (if (and (not (get-in before [:kernel-environments (:id root)]))
                                   (get-in world [:kernel-environments (:id root)]))
                            :transferred-to-world :released)))
                (when (:inherit-map @owners) (vswap! owners assoc-in [:inherit-map :status] :released))
                (save! world)
                (if-let [[receipt node]
                         (when checked
                           (some (fn [[receipt node]]
                                   (when (every? (fn [[name ci]] (identical? ci (.lookup checked name)))
                                                 (:projected receipt)) [receipt node])) candidates))]
                  (let [root (call! (:root imports/helpers) [environment] :root)
                        map-ref (call! (:constant-map imports/helpers) [environment] :map)
                        anchor (get-in @progress [:kernel-environments (:id root)])
                        flag (call! (:quot-init? imports/helpers) [environment] nil)
                        _ (when-not (and (= root (:anchor anchor)) (= map-ref (:constant-map anchor))
                                         (identical? checked (:env anchor))
                                         (= (if (.isQuotEnabled checked) 1 0)
                                            (native/nat-value {:ref? m/ref? :node m/node} @progress flag)))
                            (fail "Completed graph target checked root/map/quotient differs" {}))
                        visibility (call! (:is-exporting reconstruction-helpers) [environment] nil)
                        _ (when-not (= 0 (native/nat-value {:ref? m/ref? :node m/node} @progress visibility))
                            (fail "Completed graph requires the actual private selected view" {}))
                        header-ref (call! (:header source/helpers) [environment] :header)
                        text (string/string-value {:ref? m/ref? :node m/node} @progress header-ref)
                        _ (when (> (count text) (:max-bytes limits))
                            (fail "Completed graph header exceeds host parsing bound" {}))
                        header (graph-json! text limits graph-limits)
                        _ (when-not (and (= "lean-source-import-header/1" (:schema header))
                                         (= "SourceModuleImport.finalizerHeader" (:producer header))
                                         (= (get prim/pinned-build "lean_get_githash") (:leanCommit header))
                                         (false? (:moduleSystem header))
                                         (= (:requested-imports receipt) (:imports header)))
                            (fail "Completed graph target import header differs" {}))
                        _ (release! :header)
                        names-ref (call! module-names-helper [environment] :module-names)
                        names (mapv #(let [encoded (structured-name-value
                                                   (bridge/project-name-bounded @progress % (:name-limits limits)))]
                                       (graph-wire-name! encoded true graph-limits))
                                    (proof-array! @progress names-ref (:max-modules graph-limits)))
                        _ (when-not (= (:module-order receipt) names)
                            (fail "Completed graph target module order differs" {}))
                        _ (release! :module-names)
                        name-ref (get-in node [:wire-names (:name row)])
                        _ (when-not name-ref (fail "Completed graph row lacks CI/extra-name attribution" {}))
                        _ (when-not (= (:name row)
                                       (structured-name-value
                                         (bridge/project-name-bounded @progress name-ref (:name-limits limits))))
                            (fail "Completed graph row Name changed at its saved Ref" {}))
                        index (call! module-index-helper [environment name-ref] :index)
                        index-node (when (m/ref? index) (m/node @progress index))
                        _ (when-not (and (= 1 (:tag index-node)) (bridge/constructor-layout? index-node 1 0)
                                         (= (:module-index receipt)
                                            (native/nat-value {:ref? m/ref? :node m/node} @progress
                                                              (first (:fields index-node)))))
                            (fail "Completed graph row belongs to another attempt module" {}))]
                    (release! :index) (release! :map) (release! :root)
                    [@progress true])
                  [@progress false]))
              (catch Throwable cause
                (throw (ex-info (or (.getMessage cause) "Completed source graph proof failed")
                                (merge {:checkpoint @progress} (ex-data cause)
                                       {:source-graph-proof-owners @owners}) cause))))))))))

(defn- graph-planner-limits [limits]
  {:max-modules (:max-modules limits) :max-roots (:max-roots limits)
   :max-edges (:max-edges limits) :max-depth (:max-depth limits) :max-names (:max-names limits)
   :max-name-nodes (:max-name-nodes limits) :max-name-chars (:max-name-bytes limits)
   :max-total-name-chars (:max-total-name-bytes limits)})

(defn- graph-data-arrays [world value maximum]
  (let [node (when (m/ref? value) (m/node world value))]
    (when-not (and (= 0 (:tag node)) (bridge/constructor-layout? node 5 1))
      (fail "Source graph requires actual ModuleData layout" {}))
    (let [[_ names constants extras] (:fields node)
          names (proof-array! world names maximum) constants (proof-array! world constants maximum)
          extras (proof-array! world extras maximum)]
      (when-not (= (count names) (count constants))
        (fail "Source graph ModuleData CI/name arrays differ" {}))
      (let [flag (m/read-scalar-node node {:index 5 :offset 0 :type "uint8" :region :scalar})]
        (when-not (or (= 0 flag) (= 1 flag))
          (fail "Source graph ModuleData isModule is not a Bool" {}))
        {:names names :constants constants :extras extras :module? (= 1 flag)}))))

(defn- graph-native-arrays [world prefix limits]
  (when-not (and (vector? (:modules prefix)) (<= (count (:modules prefix)) (:max-modules limits)))
    (fail "Source graph native module inventory exceeds bound" {}))
  (mapv (fn [module]
          (let [parts (:parts module) ir-parts (:irParts module)]
            (when-not (and (vector? parts) (<= 1 (count parts) 3)
                           (vector? ir-parts) (<= (count ir-parts) 2) (true? (:hasData module)))
              (fail "Source graph native data parts are incomplete" {}))
            (let [public (graph-data-arrays world (:value (first parts)) (:max-names limits))
                  private (if (:module? public)
                            (do (when-not (= 3 (count parts))
                                  (fail "Source graph native private data part is missing" {}))
                                (graph-data-arrays world (:value (nth parts 2)) (:max-names limits))) public)
                  ir (if (and (:module? private) (seq ir-parts))
                       (graph-data-arrays world (:value (peek ir-parts)) (:max-names limits)) private)]
              {:module (:module module) :names (:names private) :extras (:extras ir)}))) (:modules prefix)))

(defn- graph-selected-name-count [native descriptors request-count]
  ;; Count occurrences, not unique names. Keep preparation and finishing policy
  ;; gates identical, including module-name and request-name overhead.
  (reduce +' (+' request-count (count descriptors))
          (concat (map #(+' 2 (count (:names %)) (count (:extras %))) native)
                  (map #(+' 2 (count (:dependencies %)) (count (:const-names %))
                             (count (:extra-names %))) descriptors))))

(defn- graph-plan-selection!
  "Only private authenticated node data enters here. G0 remains descriptive;
   exact G1 Name occurrences/UTF-8/key budgets are checked in addition to G0."
  [world prefix p nodes root-descriptors]
  (let [limits (:graph-limits p) native (graph-native-arrays world prefix limits)
        descriptors (mapv :descriptor nodes)
        requests (into source/init-requests (map #(hash-map :module (:module %) :importAll false
                                                          :isExported true :isMeta false)) root-descriptors)
        names (graph-selected-name-count native descriptors (count requests))
        _ (when (or (> (+ (count native) (count nodes)) (:max-modules limits))
                    (> (count root-descriptors) (:max-roots limits)) (> names (:max-names limits)))
            (fail "Source graph selected module/root/Name inventory exceeds bounds" {}))
        total (volatile! 0)
        project (fn [value]
                  (let [remaining (- (:max-total-name-bytes limits) @total)
                        name-limits (-> (get-in p [:limits :name-limits])
                                        (update :max-nodes min (:max-name-nodes limits))
                                        (update :max-chars min (:max-name-bytes limits) remaining))
                        encoded (structured-name-value (bridge/project-name-bounded world value name-limits))]
                    (graph-wire-name! encoded false limits total)))
        native (mapv (fn [{:keys [module names extras]}]
                       ;; G1 checks prefix moduleNames and each selected record.
                       (graph-wire-name! module true limits total)
                       (graph-wire-name! module true limits total)
                       {:module module :const-names (mapv project names) :extra-names (mapv project extras)}) native)
        keys-total (volatile! 0)]
    (doseq [[node descriptor] (map vector nodes descriptors)]
      (graph-wire-name! (:module descriptor) true limits total)
      (doseq [request (into source/init-requests
                           (map #(hash-map :module (:module %) :importAll false :isExported true :isMeta false))
                           (:dependencies descriptor))]
        (graph-wire-name! (:module request) true limits total))
      (doseq [name (concat (:const-names descriptor) (:extra-names descriptor))]
        (graph-wire-name! name false limits total))
      (let [key (get-in node [:entry :key]) remaining (- (:max-total-key-bytes limits) @keys-total)]
        (when-not (and (string? key) (pos? (count key))
                       (<= (count key) (min (:max-key-bytes limits) remaining)))
          (fail "Source graph region key exceeds bound" {}))
        (vswap! keys-total +' (graph-utf8-size! key (min (:max-key-bytes limits) remaining)))))
    (doseq [request requests] (graph-wire-name! (:module request) true limits total))
    (when (> (reduce +' (count (:constants prefix))
                     (map #(count (get-in % [:proof :constants])) nodes))
             (get-in p [:limits :max-constants]))
      (fail "Source graph selected CI union exceeds its constant bound" {}))
    (let [plan (graph-plan/plan native descriptors root-descriptors (graph-planner-limits limits))
          by-module (into {} (map (juxt :module identity)) nodes)]
      {:plan plan :nodes (mapv by-module (:source-order plan)) :requested-imports requests
       :name-count names :name-bytes @total :key-bytes @keys-total
       :constants (reduce (fn [out node] (merge out (get-in node [:proof :constants])))
                          (:constants prefix) nodes)})))

(defn- graph-resolve!
  "Resolve capabilities by identity before providing bounded descriptors to G0.
   Module/version conflicts and exact dependency order are checked by G0; there
   is no branch-heap merge and no caller-supplied topology or version digest."
  [world prefix-cap prefix p roots]
  (when-not (and (vector? roots) (<= (count roots) (get-in p [:graph-limits :max-roots])))
    (fail "Source graph requires bounded ordered root capabilities" {}))
  (let [limit (get-in p [:graph-limits :max-modules])
        source-evidence (volatile! nil)
        issued (loop [pending (vec (rseq roots)) seen #{} nodes [] edges 0]
                (if (empty? pending) nodes
                  (let [cap (peek pending) pending (pop pending) node (graph-node! cap)]
                    (when-not (and (identical? (:profile-token node) (:token p))
                                   (identical? prefix-cap (:prefix node))
                                   (identical? (:source prefix) (:source node)))
                      (fail "Source graph roots mix profile/prefix/Native Source identities" {}))
                    (if (contains? seen cap) (recur pending seen nodes edges)
                      (let [parents (:parents node) next-edges (+' edges (count parents))]
                        (when-not (and (vector? parents) (< (+ (count (:modules prefix)) (count nodes)) limit)
                                       (<= next-edges (get-in p [:graph-limits :max-edges])))
                          (fail "Source graph closure exceeds module/edge bounds" {}))
                        (graph-entry-matches! world node true source-evidence)
                        (recur (into pending (rseq parents)) (conj seen cap) (conj nodes [cap node]) next-edges))))))
        nodes (mapv second issued)
        roots (mapv (fn [cap] (select-keys (:descriptor (graph-node! cap)) [:module :version])) roots)]
    (assoc (graph-plan-selection! world prefix p nodes roots)
           :caps-by-module (into {} (map (fn [[cap node]] [(:module node) cap])) issued))))

(defn- graph-proof-budgets! [budgets]
  (when-not (and (map? budgets) (= 2 (count budgets))
                 (= #{:helper-fuel :attempt-fuel} (set (keys budgets))))
    (fail "Source graph proof requires explicit helper/aggregate fuel" {}))
  (doseq [[key value] budgets] (positive-long! value key))
  budgets)

(defn- graph-budget-operation!
  "Private fixed-call adapter. Reserve before effects; save returned packet
   before charging. Failed calls keep actual checkpoint/session and poison the
   attempt; an unknown failure retains its entire reservation, never retries."
  [state budgets label operation]
  (let [world (:world @state) session (:session @state) bound (:helper-fuel budgets)]
    (when (:budget-poisoned? @state) (fail "Source graph proof attempt is poisoned" {}))
    (when (> bound (- (:attempt-fuel budgets) (:used @state)))
      (fail "Source graph proof cannot reserve next helper" {:reservation bound}))
    (swap! state assoc :reserved bound :phase :proof-helper-started)
    (try
      (let [result (operation (assoc session :fuel bound) world)
            _ (swap! state assoc :world (:world result) :session (:session result)
                     :last-operation {:label label :returned result})
            delta (- (get-in result [:world :stats :steps]) (get-in world [:stats :steps]))]
        (when-not (<= 0 delta bound) (fail "Source graph helper charge is invalid" {}))
        (swap! state #(-> % (update :used +' delta) (assoc :reserved 0 :phase :proof-helper-completed)))
        result)
      (catch Throwable cause
        (let [data (ex-data cause)
              latest (or (:checkpoint data) (:world @state))
              delta (when (and (contains? data :checkpoint) (get-in latest [:stats :steps]))
                      (- (get-in latest [:stats :steps]) (get-in world [:stats :steps])))]
          (swap! state assoc :world latest :session (or (:checkpoint-session data) (:session @state))
                 :budget-poisoned? true :phase :proof-helper-failed
                 :failed-operation {:label label :cause cause :observed-steps delta})
          (when (and delta (<= 0 delta bound))
            (swap! state #(-> % (update :used +' delta) (assoc :reserved 0))))
        (throw cause))))))

(defn- graph-invocation [state budgets]
  (fn [world target args]
    (swap! state assoc :world world)
    (let [before (:used @state)]
      (try
        (let [result (graph-budget-operation! state budgets {:target target :arguments args}
                       (fn [session world]
                         (let [called (raw/call session world target args)]
                           {:world (:state called) :session (:session called) :value (:value called)
                            :raw-result called})))]
          [(:world result) (:value result)])
        (finally
          ;; Charge only observed work, including a known partial failure. An
          ;; unknown failed reservation remains reserved by the budget adapter.
          ;; Publication proof states have no graph-operation marker.
          (when (or (:graph-operation? @state) (:native-operation? @state))
            (swap! state update :helper-steps +' (- (:used @state) before))))))))

(defn- graph-current-receipt!
  "Use THIS world's latest receipt and THIS checked base's Java projections;
   never reuse a local Java CI from an earlier node publication/import attempt."
  [world p node ^Env checked selection source-evidence]
  (let [entry (graph-entry-matches! world node true source-evidence)
        receipt (graph-receipt! (:graph-import entry))
        issued-node (graph-node! (:node receipt))
        anchor (get-in world [:kernel-environments (:id (:anchor receipt))])]
    (when-not (and (identical? node issued-node)
                   (identical? (:token p) (:profile-token receipt))
                   (= (:anchor receipt) (:anchor anchor)) (= (:constant-map receipt) (:constant-map anchor))
                   (identical? (:checked-env receipt) (:env anchor))
                   (= (:module-order receipt) (get-in selection [:plan :module-order]))
                   (= (:requested-imports receipt) (:requested-imports selection))
                   (= (:module-index receipt) (get-in selection [:plan :module-indices (:module node)]))
                   (= (get-in node [:proof :constants]) (:constants receipt))
                   (every? (fn [[name ci]] (identical? ci (.lookup checked name))) (:projected receipt)))
      (fail "Source graph parent is not inherited from its current completed import" {}))
    receipt))

(defn- graph-observe-checked-union!
  "Prove the actual private checked union/header/order. Compilation additionally
   requires CURRENT parent receipts; a newly checked import uses fresh local
   Java projections without demanding any earlier receipt or projection."
  [world invoke environment prefix certificate p selection current-receipts?]
  (let [progress (volatile! world) owners (volatile! {}) source-evidence (volatile! nil)
        call! (fn [target args owner]
                (let [[world value] (invoke @progress target args)]
                  (vreset! progress world)
                  (when owner (vswap! owners assoc owner {:value value :status :owned})) value))
        release! (fn [owner]
                   (vreset! progress (m/release @progress (get-in @owners [owner :value]) 1))
                   (vswap! owners assoc-in [owner :status] :released))]
    (try
      (let [root (call! (:root imports/helpers) [environment] :root)
            anchor (get-in @progress [:kernel-environments (:id root)])
            ^Env checked (:env anchor)
            map-ref (call! (:constant-map imports/helpers) [environment] :map)
            flag (call! (:quot-init? imports/helpers) [environment] nil)
            flag (native/nat-value {:ref? m/ref? :node m/node} @progress flag)
            expected (:constants selection)
            _ (when-not (and (m/ref? root) (= root (:anchor anchor)) (instance? Env checked)
                             (m/ref? map-ref) (= map-ref (:constant-map anchor))
                             (= flag (if (.isQuotEnabled checked) 1 0))
                             (= (:quot-init? anchor) (.isQuotEnabled checked)))
                (fail "Source graph input has no exact protected checked base" {}))
            values-ref (call! (:constants imports/helpers) [environment] :constants)
            values (proof-array! @progress values-ref (get-in p [:limits :max-constants]))
            _ (when-not (and (= (count values) (count expected) (count (set values)))
                             (= (set values) (set (vals expected)))
                             (= (count expected) (count (.allConstants checked))))
                (fail "Source graph input is not exact native plus selected parent CI union" {}))
            _ (doseq [[name ci] (:projected certificate)]
                (when-not (identical? ci (.lookup checked name))
                  (fail "Source graph input replaced an original native Java CI" {})))
            visibility (call! (:is-exporting reconstruction-helpers) [environment] nil)
            _ (when-not (= 0 (native/nat-value {:ref? m/ref? :node m/node} @progress visibility))
                (fail "Source graph input is not the private selected view" {}))
            header-ref (call! (:header source/helpers) [environment] :header)
            text (string/string-value {:ref? m/ref? :node m/node} @progress header-ref)
            _ (when (> (count text) (get-in p [:limits :max-bytes]))
                (fail "Source graph input header exceeds parsing bound" {}))
            header (graph-json! text (:limits p) (:graph-limits p))
            _ (when-not (and (= "lean-source-import-header/1" (:schema header))
                             (= "SourceModuleImport.finalizerHeader" (:producer header))
                             (= (get prim/pinned-build "lean_get_githash") (:leanCommit header))
                             (false? (:moduleSystem header))
                             (= (:requested-imports selection) (:imports header)))
                (fail "Source graph input has another import header" {}))
            names-ref (call! module-names-helper [environment] :module-names)
            names (mapv #(graph-wire-name!
                           (structured-name-value
                             (bridge/project-name-bounded @progress % (get-in p [:limits :name-limits])))
                           true (:graph-limits p))
                        (proof-array! @progress names-ref (get-in p [:graph-limits :max-modules])))
            _ (when-not (= names (get-in selection [:plan :module-order]))
                (fail "Source graph input has another ordered module closure" {}))
            receipts (when current-receipts?
                       (mapv #(graph-current-receipt! @progress p % checked selection source-evidence) (:nodes selection)))
            projected (if current-receipts?
                        (reduce (fn [out receipt] (merge out (:projected receipt))) (:projected certificate) receipts)
                        (into {} (map (fn [[name _]]
                                        (let [ci (.lookup checked name)]
                                          (when-not (and ci (= name (.name ^ConstantInfo ci)))
                                            (fail "Fresh graph union lacks an expected Java ConstantInfo" {}))
                                          [name ci]))) expected))]
        (release! :module-names) (release! :header) (release! :constants) (release! :map) (release! :root)
        {:world @progress :constants expected :projected projected :checked-env checked
         :anchor root :anchor-entry anchor :constant-map map-ref :quot-init? (= 1 flag)
         :module-order names :requested-imports (:requested-imports selection)})
      (catch Throwable cause
        (throw (ex-info (or (.getMessage cause) "Source graph input-base proof failed")
                        (merge {:checkpoint @progress} (ex-data cause)
                               {:source-graph-base-owners @owners}) cause))))))


(defn- graph-observe-base!
  "Fixed compilation adapter: require exact current parent receipt inheritance."
  [world invoke environment prefix certificate p selection]
  (graph-observe-checked-union! world invoke environment prefix certificate p selection true))

(defn- compact-graph-proof [proof before]
  ;; Successful node authority has no preparedWorld, original JavaEnv, imported
  ;; parent receipt, or publication Context. The failure path keeps those exact
  ;; operation packets separately. Existing legacy proof storage is unchanged.
  (-> (select-keys proof [:entry :unit :unit-digest :module :constants :guest-names :admission])
      (assoc-in [:admission :baseline]
                {:functions (:functions before)
                 :eval-const-authorizations (select-keys (:eval-const-authorizations before) admission-keys)})))

(defn- graph-capture-request! [request p]
  ;; The existing compiler's source IO/compilation budget is independent of the
  ;; bounded proof helpers. Bound new host Name/key work before the old capture.
  (when-not (and (map? request) (<= (count request) 6)
                 (vector? (:roots request))
                 (<= (count (:roots request)) (get-in p [:limits :max-declarations])))
    (fail "Source graph requires a bounded explicit deferred compilation request" {}))
  (graph-java-name! (:module-name request) true (:graph-limits p))
  (doseq [name (:roots request)] (graph-java-name! name false (:graph-limits p)))
  (capture-import-request request))

(def ^:private classic-header-limit-keys
  #{:max-source-bytes :max-file-name-bytes :max-output-bytes :max-json-depth
    :max-imports :max-diagnostics :max-name-nodes :max-name-bytes :max-total-name-bytes})

(defn- classic-header-limits! [limits]
  (when-not (and (map? limits) (= 9 (count limits))
                 (every? #(contains? limits %) classic-header-limit-keys))
    (fail "Classic header discovery requires nine explicit bounds" {}))
  (doseq [[key value] limits] (positive-long! value key))
  (when-not (<= 2 (:max-imports limits) 1026)
    (fail "Classic header discovery supports at most 1024 ordinary dependencies" {}))
  limits)

(defn- classic-header-envelope! [text captured limits]
  (let [header (bounded-header-json! text (:max-output-bytes limits) (:max-json-depth limits))
        requests (:requestedImports header)]
    (when-not (and (= "lean-file-header/1" (:schema header))
                   (= "RuntimeCompileShim.inspectFileHeader" (:producer header))
                   (= (get prim/pinned-build "lean_get_githash") (:leanCommit header))
                   (= {:target "x86_64-unknown-linux-gnu" :wordBits 64} (:runtimeProfile header))
                   (= (:file-name captured) (:fileName header))
                   (false? (:moduleSystem header)) (boolean? (:hasErrors header))
                   (integer? (:headerEndByte header))
                   (<= 0 (:headerEndByte header)
                       (or (:source-byte-length captured)
                           (graph-utf8-size! (:text captured) Long/MAX_VALUE)))
                   (vector? (:diagnostics header)) (<= (count (:diagnostics header)) (:max-diagnostics limits))
                   (every? map? (:diagnostics header))
                   (vector? requests) (<= (count requests) (:max-imports limits)))
      (fail "Expected a bounded actual classic header from the pinned parser" {}))
    (if (:hasErrors header)
      (when-not (empty? requests)
        (fail "An erroneous classic header cannot describe imports" {}))
      (do
        ;; Bound Names before the fixed classic flag validator compares them.
        (let [total (volatile! 0)]
          (doseq [request requests]
            (graph-wire-name! (:module request) true limits total)))
        (source/validate-graph-imports! requests)))
    header))

(defn- read-classic-header-result! [state world wrapper captured limits]
  ;; Escrow the actual IO owner BEFORE even inspecting its layout or payload.
  (swap! state assoc :world world :header-result {:value wrapper :status :owned})
  (let [node (when (m/ref? wrapper) (m/node world wrapper))]
    (when-not (and (= :ctor (:kind node)) (= 0 (:tag node)) (= 1 (count (:fields node)))
                   (nil? (:layout node)) (empty? (:scalar-bytes node)))
      (fail "Classic header parser did not return an owned IO.Result.ok String" {}))
    (classic-header-envelope!
      (string/string-value {:ref? m/ref? :node m/node} world (first (:fields node))) captured limits)))

(defn- release-classic-header-result! [state wrapper]
  (let [released (assoc (m/release (:world @state) wrapper 1) :result 0)]
    (swap! state assoc :world released :header-result {:value wrapper :status :released})
    released))

(defn- graph-inspect-header! [state invoke captured p expected-imports]
  (let [[world wrapper] (invoke (:world @state) frontend/header-target
                               [(:text captured) (:file-name captured) m/erased])
        limits {:max-output-bytes (get-in p [:limits :max-bytes])
                :max-json-depth (+' 32 (get-in p [:graph-limits :max-name-nodes]))
                :max-imports (+ 2 (get-in p [:graph-limits :max-roots]))
                :max-diagnostics (get-in p [:limits :max-declarations])
                :max-name-nodes (get-in p [:graph-limits :max-name-nodes])
                :max-name-bytes (get-in p [:graph-limits :max-name-bytes])
                :max-total-name-bytes (get-in p [:graph-limits :max-total-name-bytes])}
        header (read-classic-header-result! state world wrapper captured limits)]
    (when-not (false? (:hasErrors header))
      (fail "Source graph requires a successful actual classic header from the pinned parser" {}))
    (when-not (= expected-imports (:requestedImports header))
      (fail "Source graph header differs from its exact ordered parent selection" {}))
    (release-classic-header-result! state wrapper)
    header))

(defn discover-classic-source-header
  "Run ONE fixed pinned header helper on immutable host TEXT/FILE-NAME strings.
   OPTIONS is exactly {:configuration independent-resident-configuration :limits
   nine-explicit-header-bounds :budgets {:helper-fuel n :attempt-fuel n}}. Return
   {:packet updated-owned-packet :request captured :header descriptive :status
   :ok-or-header-error :progress scalar-work}. The ordinary classic subset has
   implicit Init/meta Init and ordinary dependencies; prelude/module-system files
   are outside this slice. Valid parser errors return diagnostics and NO imports.

   No adoption, import, receipt, publication or graph permission occurs. Thread
   the returned packet through ONE scratch branch, then adopt once; helper work
   may change globals/World and must not be discarded. The aggregate budget covers
   this operation's one helper and its nested guest calls, NOT Project discovery
   or compilation as a whole. Project must reserve/charge its remaining aggregate
   around every operation. Success restores only incoming session :fuel policy,
   preserving actual child caches/registries; failure retains actual helper policy,
   exact owner/checkpoint/session and known charge or unknown full reservation.
   This function never closes borrowed resources or automatically retries."
  [packet request {:keys [configuration limits budgets] :as options}]
  (let [state (atom {:phase :entry :entry packet :world (:world packet) :session (:session packet)
                     :used 0 :reserved 0})]
    (try
      (when-not (and (map? options) (= 3 (count options))
                     (contains? options :configuration) (contains? options :limits) (contains? options :budgets))
        (fail "Classic header discovery requires fixed configuration, bounds and budgets" {}))
      (classic-header-limits! limits)
      (graph-proof-budgets! budgets)
      (when-not (and (map? request) (= 2 (count request))
                     (contains? request :text) (contains? request :file-name)
                     (string? (:text request)) (string? (:file-name request)) (seq (:file-name request)))
        (fail "Classic header discovery requires one immutable text/file-name snapshot" {}))
      ;; Count gates precede Unicode scans; no filesystem reads or guest String
      ;; projections are implicit in this public discovery operation.
      (let [sizes (mapv (fn [[value bound]]
                          (when (> (count value) bound) (fail "Classic header input exceeds byte bound" {}))
                          (graph-utf8-size! value bound))
                        [[(:text request) (:max-source-bytes limits)]
                         [(:file-name request) (:max-file-name-bytes limits)]])]
        (swap! state assoc :source-byte-length (first sizes)))
      (swap! state assoc :request request :phase :readiness)
      (resident/adoption-readiness! packet configuration)
      (eval/validate-executables! (:world packet) (:trusted-functions configuration) [frontend/header-target])
      (let [called (graph-budget-operation! state budgets :classic-header
                     (fn [session world]
                       (let [result (raw/call session world frontend/header-target
                                              [(:text request) (:file-name request) m/erased])]
                         {:world (:state result) :session (:session result) :value (:value result)
                          :raw-result result})))
            header (read-classic-header-result! state (:world called) (:value called)
                     (assoc request :source-byte-length (:source-byte-length @state)) limits)
            _ (swap! state assoc :phase :release-header-result)
            world (release-classic-header-result! state (:value called))
            ;; Preserve the release checkpoint before restoring the separate
            ;; caller policy used by later compilation, or constructing results.
            _ (swap! state assoc :phase :header-result-released)
            session (assoc (:session @state) :fuel (get-in packet [:session :fuel]))
            status (if (:hasErrors header) :header-error :ok)
            result {:packet (assoc packet :world world :session session) :request request :header header :status status
                    :progress {:phase :completed :guest-steps (:used @state) :helper-steps (:used @state)
                               :reserved (:reserved @state) :helper-calls 1}}]
        result)
      (catch Throwable cause
        (let [data (ex-data cause)
              diagnostic @state]
          (throw (ex-info (or (.getMessage cause) "Classic header discovery failed")
                   (merge data {:checkpoint (or (:checkpoint data) (:world diagnostic))
                                :checkpoint-session (or (:checkpoint-session data) (:session diagnostic))
                                :classic-header-discovery-state diagnostic}) cause)))))))

(defn- graph-new-node-descriptor!
  "Check aggregate inventory BEFORE projecting own names. This name/byte delta
   replaces old requested parent names with identical own dependency names;
   only two own-module and two implicit Init occurrences are additionally new."
  [world entry module parents selection p version]
  (let [limits (:graph-limits p)
        {:keys [names constants extras module?]} (graph-data-arrays world (:data entry) (:max-names limits))
        count' (+' (:name-count selection) 4 (count names) (count extras))
        edges (+' (count parents) (reduce +' 0 (map #(count (get-in % [:descriptor :dependencies])) (:nodes selection))))]
    (when (or module? (> count' (:max-names limits))
              (> (inc (count (get-in selection [:plan :module-order]))) (:max-modules limits))
              (> edges (:max-edges limits)))
      (fail "Source graph new publication exceeds its classic module/edge/Name inventory" {}))
    (let [total (volatile! (:name-bytes selection))
          project (fn [reference]
                    (let [remaining (- (:max-total-name-bytes limits) @total)
                          _ (when-not (pos? remaining) (fail "Source graph new Name exceeds aggregate bytes" {}))
                          bounds (-> (get-in p [:limits :name-limits])
                                     (update :max-nodes min (:max-name-nodes limits))
                                     (update :max-chars min (:max-name-bytes limits) remaining))
                          value (bridge/project-name-bounded world reference bounds)]
                      (graph-wire-name! (structured-name-value value) false limits total)))]
      (dotimes [_ 2] (graph-wire-name! module true limits total))
      (doseq [request source/init-requests] (graph-wire-name! (:module request) true limits total))
      {:module module :version version
       :dependencies (mapv #(select-keys (:descriptor %) [:module :version]) parents)
       :const-names (mapv project names) :extra-names (mapv project extras)})))

(defn publish-source-graph-node
  "Compile/publish ONCE from the exact completed checked parent base, then seal
   its owned ModuleData and every new initializer-free unit. PARENTS are ordered
   issued node capabilities. OPTIONS is exactly {:proof-budgets {:helper-fuel n
   :attempt-fuel n}}. The aggregate bounds only new proof/header guest helpers;
   existing source compilation/publication and resident adoption retain their
   independent per-call budgets. No completed receipt or partial graph permission
   is issued. Failures retain exact operation packets and are never resumed here."
  [context request prefix profile parents {:keys [proof-budgets] :as options}]
  (locking context
    (let [state (atom {:phase :entry :used 0 :reserved 0})]
      (try
        (when-not (and (map? options) (= 1 (count options)) (contains? options :proof-budgets))
          (fail "Source graph publication requires only explicit proof-helper budgets" {}))
        (graph-proof-budgets! proof-budgets)
        (let [entry (resident/snapshot context)
              _ (swap! state assoc :entry entry :world (:world entry) :session (:session entry))
              {raw-prefix :prefix :keys [certificate configuration graph-profile]} (graph-readiness! entry prefix profile)
              p graph-profile
              captured (graph-capture-request! request p)
              module (graph-java-name! (:module-name captured) true (:graph-limits p))
              _ (when (get-in entry [:world :source-modules module])
                  (fail "Source graph publication must start before that module version is registered" {}))
              selection (graph-resolve! (:world entry) prefix raw-prefix p parents)
              _ (swap! state assoc :selection selection :captured-request captured :phase :header-started)
              invoke (graph-invocation state proof-budgets)
              _ (graph-inspect-header! state invoke captured p (:requested-imports selection))
              _ (swap! state assoc :phase :current-parent-base-proof)
              base (graph-observe-base! (:world @state) invoke (:environment entry) raw-prefix certificate p selection)
              _ (swap! state assoc :world (:world base) :current-base base)
              pre-packet (assoc entry :world (:world @state)
                                :session (assoc (:session @state) :fuel (get-in entry [:session :fuel])))
              _ (swap! state assoc :precompile-adoption-entry pre-packet :phase :precompile-adoption-started)
              pre-context (resident/adopt-prepared pre-packet configuration)
              _ (swap! state assoc :precompile-context pre-context :phase :precompile-adoption-returned)
              before (resident/snapshot pre-context)
              _ (swap! state assoc :precompile-entry before :world (:world before) :session (:session before)
                       :phase :compilation-started)
              result (publication/load-and-publish-graph pre-context captured
                        {:configuration configuration :expected-imports (:requested-imports selection)})
              _ (swap! state assoc :publication-result result :phase :compilation-returned)
              original (resident/snapshot (:context result))
              _ (swap! state assoc :original-publication original :world (:world original) :session (:session original))
              _ (when-not (:success result) (fail "Source graph node requires successful actual source publication" {}))
              source-entry (get-in original [:world :source-modules module])
              ;; This ORIGINAL publication snapshot is the anchor for both graph
              ;; payload and Java/guest identity; never substitute a later view.
              data-graph (local-ci-graph! (:world original) [(:data source-entry)] (:limits p))
              parent-data (mapv graph-node! parents)
              version (Object.)
              descriptor (graph-new-node-descriptor! (:world original) source-entry module parent-data selection p version)
              proved (publication-proof-with-base! original raw-prefix certificate module invoke
                       (select-keys (:limits p) [:max-constants :name-limits])
                       {:profile :graph :imports (:requested-imports selection)
                        :constants (:constants base) :projected (:projected base) :allow-const-extra? true})
              _ (swap! state assoc :world (:world proved) :rich-publication-proof (:proof proved) :phase :publication-proof-complete)
              admission (capture-publication-admission! (:world before) (:world original) (:proof proved) (:limits p))
              proof (compact-graph-proof (assoc (:proof proved) :admission admission) (:world before))
              node {:profile-token (:token p) :prefix prefix :source (:source raw-prefix)
                    :configuration configuration :module module :parents parents :descriptor descriptor
                    :entry source-entry :proof proof :data-graph data-graph
                    :limits (:limits p) :host-limits (:host-limits p)
                    :wire-names (into {} (map (fn [[name reference]] [(graph-java-name! name false (:graph-limits p)) reference]))
                                      (:guest-names proof))}
              ;; Selected parent capabilities plus separate private version token
              ;; avoid a weak-registry value -> own Node key cycle. This plan is
              ;; descriptive only; all authority still comes from issuance below.
              own-selection (graph-plan-selection! (:world original) raw-prefix p
                              (conj (:nodes selection) node) [(select-keys descriptor [:module :version])])
              _ (when-not (= data-graph (local-ci-graph! (:world @state) [(:data source-entry)] (:limits p)))
                  (fail "Source graph publication payload changed during its proof" {}))
              next-packet (assoc original :world (:world @state)
                                 :session (assoc (:session @state) :fuel (get-in original [:session :fuel])))
              _ (swap! state assoc :adoption-entry next-packet :phase :adoption-started)
              next-context (resident/adopt-prepared next-packet configuration)
              _ (swap! state assoc :adopted-context next-context :phase :adoption-returned)
              adopted (resident/snapshot next-context)
              _ (swap! state assoc :adopted-entry adopted :world (:world adopted) :session (:session adopted))
              _ (graph-entry-matches! (:world adopted) node)
              ;; All fallible operations and public result construction precede
              ;; issuance. The successful private node retains no old packets,
              ;; parent receipt/JavaEnv, original result, or the own cap key.
              cap (SourceGraphNode.)
              public-result (assoc result :context next-context :graph-node cap
                             :graph-publication {:module module :parents (mapv :module parent-data)
                                                 :unit-count (count (:units admission))
                                                 :row-count (count (:rows admission))
                                                 :constant-count (count (:constants proof))
                                                 :source-order (get-in own-selection [:plan :source-order])})]
          (locking graph-nodes (.put graph-nodes cap node))
          public-result)
        (catch Throwable cause
          (let [data (ex-data cause)]
            (when (:checkpoint data) (swap! state assoc :world (:checkpoint data)))
            (when (:checkpoint-session data) (swap! state assoc :session (:checkpoint-session data)))
            (swap! state assoc :phase :failed :cause cause)
            (throw (ex-info (or (.getMessage cause) "Source graph publication failed")
                            (merge {:checkpoint (:world @state) :checkpoint-session (:session @state)} data
                                   {:source-graph-publication-state @state :source-graph-publication-terminal? true}) cause))))))))

;; Staged graph imports use the same private cooperative driver through fixed
;; legacy/graph adapters. No graph operation enters reconstruction callback scope.
(defn- graph-own! [state label operation]
  (let [[world value] (operation (:world @state))]
    (swap! state #(-> % (assoc :world world)
                     (assoc-in [:source-graph :owners label] {:value value :state :owned})))
    value))

(defn- graph-retain! [state label value]
  (graph-own! state label (fn [world] [(m/retain world value 1) value])))

(defn- graph-transfer! [state labels]
  (doseq [label labels]
    (when-not (= :owned (get-in @state [:source-graph :owners label :state]))
      (fail "Source graph transfer lacks its exact temporary owner" {})))
  (swap! state (fn [data]
                 (reduce #(assoc-in %1 [:source-graph :owners %2 :state] :transferred) data labels))))

(defn- graph-release! [state label]
  (let [{:keys [value] status :state} (get-in @state [:source-graph :owners label])]
    (when-not (= :owned status) (fail "Source graph temporary owner is not releasable" {}))
    (let [world (m/release (:world @state) value 1)]
      ;; Record the post-release World AND transition before any later effect.
      (swap! state #(-> % (assoc :world world)
                       (assoc-in [:source-graph :owners label :state] :released))))))

(defn- graph-import-inputs! [state invoke selection p]
  (let [nodes (:nodes selection) requests (:requested-imports selection)
        modules (into (mapv :module nodes) (map :module requests))
        names (mapv #(name/from-string (imports/module-string %)) modules)
        [world array] (encoding/encode-names (:world @state) invoke names)
        _ (swap! state #(-> % (assoc :world world)
                           (assoc-in [:source-graph :owners :encoded-names] {:value array :state :owned})))
        refs (proof-array! world array (+ (count nodes) (count requests)))
        _ (when-not (= (count names) (count refs)) (fail "Source graph Name encoding is incomplete" {}))
        parts
        (mapv (fn [index node]
                (let [name-label [:part-name index] data-label [:part-data index]
                      module-name (graph-retain! state name-label (nth refs index))
                      data (graph-retain! state data-label (get-in node [:entry :data]))
                      part (graph-own! state [:part index]
                             #(m/allocate % :ctor 0 [module-name data (get-in node [:entry :key])]))]
                  (graph-transfer! state [name-label data-label])
                  part)) (range) nodes)
        parts-array (graph-own! state :parts-input #(m/allocate % :array 246 parts))
        _ (graph-transfer! state (mapv #(vector :part %) (range (count parts))))
        request-values
        (mapv (fn [index request]
                (let [label [:request-name index]
                      module-name (graph-retain! state label (nth refs (+ (count nodes) index)))
                      value (graph-own! state [:request index]
                              (fn [world]
                                (let [[world value] (m/scalar-constructor world 0 [module-name]
                                                     {:objects 1 :usize 0 :ssize 3})
                                      node (reduce (fn [node [offset flag]]
                                                     (m/write-scalar-node node
                                                       {:index 1 :offset offset :type "uint8" :region :scalar}
                                                       (if flag 1 0)))
                                                   (m/node world value)
                                                   (map-indexed vector (map request [:importAll :isExported :isMeta])))]
                                  [(m/replace-node world value node) value])))]
                  (graph-transfer! state [label])
                  value)) (range) requests)
        requests-array (graph-own! state :requests-input #(m/allocate % :array 246 request-values))
        _ (graph-transfer! state (mapv #(vector :request %) (range (count request-values))))
        limits (graph-own! state :limits-input
                 #(m/allocate % :ctor 0
                    (mapv (:graph-limits p)
                      [:max-modules :max-roots :max-edges :max-depth :max-names
                       :max-name-nodes :max-name-bytes :max-total-name-bytes
                       :max-key-bytes :max-total-key-bytes])))]
    (graph-release! state :encoded-names)
    {:parts parts-array :requests requests-array :limits limits}))

(defn- graph-anchor-regions! [state regions nodes]
  (let [values (proof-array! (:world @state) regions (count nodes))]
    (when-not (= (count values) (count nodes)) (fail "Source graph region inventory differs from selected nodes" {}))
    (doseq [[index node region] (map vector (range) nodes values)]
      (let [world (:world @state) payload (when (m/ref? region) (m/node world region))
            _ (when-not (and (= :ctor (:kind payload)) (= 0 (:tag payload))
                             (= {:objects 2 :usize 3 :ssize 1} (:layout payload))
                             (= 2 (count (:fields payload))))
                (fail "Source graph region has another packed layout" {}))
            [path data] (:fields payload) key (get-in node [:entry :key])
            text (string/string-value {:ref? m/ref? :node m/node} world path)]
        (when-not (and (not (contains? (get-in world [:source-regions key :anchors]) (:id region)))
                       (not (m/native-reference? world region))
                       (= text key) (= data (get-in node [:entry :data]))
                       (= data (get-in world [:source-regions key :data]))
                       (= 0 (m/read-scalar-node payload {:index 2 :offset 0 :type "usize" :region :usize}))
                       (= 0 (m/read-scalar-node payload {:index 3 :offset 0 :type "usize" :region :usize}))
                       (= 0 (m/read-scalar-node payload {:index 4 :offset 0 :type "usize" :region :usize}))
                       (= 0 (m/read-scalar-node payload {:index 5 :offset 0 :type "uint8" :region :scalar})))
          (fail "Source graph helper returned another logical owned region" {}))
        (graph-retain! state [:region-anchor index] region)
        (swap! state assoc-in [:world :source-regions key :anchors (:id region)] region)
        (graph-transfer! state [[:region-anchor index]])))))

(defn prepare-source-graph-import
  "Prepare a completed-only ordinary graph import from ordered issued ROOTS.
   REQUEST is captured once and its actual guest header must match ROOTS exactly.
   OPTIONS is exactly the explicit kernel policy and outer/helper/attempt budgets
   used by legacy imports. New graph preparation, finalization and proof guest
   calls share that attempt ledger; Java checker fuel remains separate policy.
   No finalizer, receipt or partial graph callback permission starts here."
  [context request prefix profile roots {:keys [kernel-policy budgets] :as options}]
  (locking context
    (let [state (atom {:graph-operation? true :source-graph {:owners {} :activation (AtomicBoolean. false)}
                       :phase :entry :used 0 :reserved 0 :outer-steps 0 :helper-steps 0 :operations 0
                       :owners {:input-environment :borrowed :input-options :borrowed}})]
      (try
        (when-not (and (map? options) (= 2 (count options))
                       (= #{:kernel-policy :budgets} (set (keys options))))
          (fail "Source graph import requires explicit policy and budgets only" {}))
        (import-policy! kernel-policy) (import-budgets! budgets)
        (when-not (and (vector? roots) (seq roots))
          (fail "Source graph import requires nonempty ordered issued roots" {}))
        (let [entry (resident/snapshot context)
              _ (swap! state assoc :entry entry :world (:world entry) :session (:session entry))
              {raw-prefix :prefix :keys [certificate configuration native-bindings graph-profile]}
              (graph-readiness! entry prefix profile)
              p graph-profile
              captured (graph-capture-request! request p)
              selection (graph-resolve! (:world entry) prefix raw-prefix p roots)
              _ (swap! state #(-> %
                                  (assoc :prefix raw-prefix :certificate certificate :configuration configuration
                                         :native-bindings native-bindings :kernel-policy kernel-policy :budgets budgets
                                         :request captured :phase :header-started
                                         :graph-audit {:source-node-count (count (:nodes selection))
                                                       :requested-root-count (count roots)
                                                       :native-module-count (count (:modules raw-prefix))
                                                       :receipt-count 0})
                                  (assoc-in [:source-graph :profile] profile)
                                  (assoc-in [:source-graph :profile-token] (:token p))
                                  (assoc-in [:source-graph :profile-data] p)
                                  (assoc-in [:source-graph :selection] selection)
                                  (assoc-in [:source-graph :roots] roots)))
              invoke (graph-invocation state (select-keys budgets [:helper-fuel :attempt-fuel]))
              header (graph-inspect-header! state invoke captured p (:requested-imports selection))
              _ (swap! state assoc :header header :phase :encode-inputs-started)
              inputs (graph-import-inputs! state invoke selection p)
              _ (swap! state assoc :phase :assemble-started)
              [world result] (invoke (:world @state) graph-assemble-helper
                                    [(:state raw-prefix) (:parts inputs) (:requests inputs) (:limits inputs)])
              _ (swap! state #(-> % (assoc :world world)
                                 (assoc-in [:source-graph :owners :helper-result] {:value result :state :owned})))
              node (when (m/ref? result) (m/node world result))
              _ (when-not (and (= 1 (:tag node)) (bridge/constructor-layout? node 1 0))
                  (fail "Source graph assembler did not return owned Except.ok" {}))
              assembly-node (m/node world (first (:fields node)))
              _ (when-not (and (= 0 (:tag assembly-node)) (bridge/constructor-layout? assembly-node 3 0))
                  (fail "Source graph assembler returned another GraphAssembly layout" {}))
              [assembled-state imports regions] (:fields assembly-node)
              _ (when-not (= imports (:requests inputs))
                  (fail "Source graph assembler changed its exact requested imports" {}))
              _ (graph-retain! state :assembly-state assembled-state)
              _ (graph-retain! state :assembly-imports imports)
              _ (graph-retain! state :assembly-regions regions)
              _ (graph-release! state :helper-result)
              _ (graph-anchor-regions! state regions (:nodes selection))
              _ (doseq [label [:assembly-regions :parts-input :requests-input :limits-input]]
                  (graph-release! state label))
              assembled {:status :ok :world (:world @state) :state assembled-state :imports imports
                         :prefix raw-prefix :requested-imports (:requested-imports selection)}
              _ (swap! state assoc :assembly assembled :phase :assembled)
              _ (swap! state update :owners assoc :assembly-state assembled-state :assembly-imports imports
                       :assembly-owner-state :owned-at-assembly-checkpoint)
              ;; The cooperative driver now owns these two retained fields.
              _ (graph-transfer! state [:assembly-state :assembly-imports])
              control (InitImport.)]
          (locking imports-issued (.put imports-issued control state))
          {:control control :progress (import-progress @state)})
        (catch Throwable cause (import-failure! state cause))))))

(defn- graph-attribution! [state invoke selection p environment]
  ;; Recheck every const AND extra Name against the actual finalized map. Module
  ;; indices belong to this attempt's ordered closure, never to a node forever.
  (doseq [node (:nodes selection)
          [wire reference] (:wire-names node)]
    (let [world (:world @state)
          expected (get-in selection [:plan :module-indices (:module node)])
          actual (structured-name-value
                   (bridge/project-name-bounded world reference (get-in p [:limits :name-limits])))]
      (when-not (= wire actual) (fail "Source graph attribution Name differs from its sealed payload" {}))
      (let [[world value] (invoke world module-index-helper [environment reference])
            label [:module-index (:module node) wire]
            _ (swap! state #(-> % (assoc :world world)
                               (assoc-in [:source-graph :owners label] {:value value :state :owned})))
            node (when (m/ref? value) (m/node world value))]
        (when-not (and (= 1 (:tag node)) (bridge/constructor-layout? node 1 0)
                       (= expected (native/nat-value {:ref? m/ref? :node m/node} world (first (:fields node)))))
          (fail "Source graph finalized CI/extra belongs to another module index" {}))
        (graph-release! state label)))))

(defn- finish-source-graph-operation! [state invoke]
  (let [{:keys [source-graph prefix certificate world io kernel-policy]} @state
        {:keys [profile profile-data selection roots]} source-graph
        p (graph-profile! profile)
        _ (when-not (identical? p profile-data) (fail "Source graph operation lost its issued profile" {}))
        prefix-cap (:prefix (first (:nodes selection)))
        current (graph-resolve! world prefix-cap prefix p roots)
        _ (when-not (and (= (:plan selection) (:plan current))
                         (= (:requested-imports selection) (:requested-imports current))
                         (= (:constants selection) (:constants current)))
            (fail "Source graph selection changed before fresh finalization checking" {}))
        _ (eval/validate-executables! world (get-in @state [:configuration :trusted-functions]) source-graph-roots)
        finished (imports/finish-finalization world io invoke
                   {:kernel-policy (assoc kernel-policy :projection-certificate certificate)
                    :finalizer-attestation {:requested-imports (:requested-imports selection)
                                           :header-helper (:header source/helpers)}})
        ;; Save the ACTUAL checked packet before any union/postcondition work.
        _ (swap! state #(-> % (assoc :world (:world finished))
                           (assoc-in [:source-graph :checked-candidate] finished)))]
    (when-not (= :ok (:status finished))
      (fail "Source graph finalizer returned IO error" {:checkpoint (:world finished) :io-result (:io-result finished)}))
    (swap! state update :owners assoc :final-environment (:environment finished) :final-environment-state :owned)
    (when-not (= (:constants selection) (get-in finished [:certificate :constants]))
      (fail "Fresh graph check did not contain the exact selected native/source CI union" {}))
    (let [observed (graph-observe-checked-union! (:world @state) invoke (:environment finished)
                     prefix certificate p selection false)
          _ (swap! state #(-> % (assoc :world (:world observed))
                             (assoc-in [:source-graph :checked-union] observed)))
          _ (when-not (identical? (:checked-env observed) (get-in finished [:certificate :env]))
              (fail "Source graph checked observation belongs to another fresh Java Env" {}))
          _ (graph-attribution! state invoke selection p (:environment finished))
          ;; Payload/units remain sealed after all guest proof helpers. Share the
          ;; exact immutable heap evidence only inside this validation operation.
          evidence (volatile! nil)
          _ (doseq [node (:nodes selection)] (graph-entry-matches! (:world @state) node true evidence))
          batch
          (mapv (fn [node]
                  (let [constants (get-in node [:proof :constants])
                        projected (select-keys (:projected observed) (keys constants))
                        _ (when-not (= (count constants) (count projected))
                            (fail "Source graph fresh Java subset is incomplete" {}))
                        receipt {:activation (get-in @state [:source-graph :activation])
                                 :node (get-in selection [:caps-by-module (:module node)])
                                 :profile-token (:token p) :module (:module node)
                                 :anchor (:anchor observed) :anchor-entry (:anchor-entry observed)
                                 :constant-map (:constant-map observed) :checked-env (:checked-env observed)
                                 :quot-init? (:quot-init? observed) :constants constants :projected projected
                                 :module-order (:module-order observed) :requested-imports (:requested-imports observed)
                                 :module-index (get-in selection [:plan :module-indices (:module node)])}
                        cap (SourceGraphReceipt.)]
                    {:cap cap :receipt receipt
                     :description {:module (:module node) :constant-count (count constants)
                                   :unit-count (count (get-in node [:proof :admission :units]))
                                   :module-index (:module-index receipt)}})) (:nodes selection))
          _ (swap! state assoc-in [:source-graph :candidate-batch] batch)
          ;; Compute one immutable candidate World, preserving old persistent
          ;; Worlds and replacing ONLY each selected node's latest receipt.
          candidate (reduce (fn [world {:keys [cap receipt]}]
                              (assoc-in world [:source-modules (:module receipt) :graph-import] cap))
                            (:world @state) batch)
          _ (swap! state assoc-in [:source-graph :batch-candidate-world] candidate)]
      ;; All receipts share one inactive token. Interrupted insertion/adoption
      ;; may preserve these exact diagnostic Worlds, but neither receipt lookup
      ;; nor completed-row authorization accepts them before public success.
      (locking graph-receipts
        (doseq [{:keys [cap receipt]} batch] (.put graph-receipts cap receipt)))
      (swap! state #(-> % (assoc :world candidate)
                       (assoc-in [:source-graph :batch-committed?] true)
                       (assoc-in [:graph-audit :receipt-count] (count batch))))
      (assoc finished :world candidate :source-graph-receipts (mapv :description batch)))))


;; Native Init reset is a distinct operation. No empty graph assembler, source
;; node or completed-source receipt is involved; old controls cannot consume it.
(deftype NativeInitBase [])
(defonce ^:private native-base-issued (WeakHashMap.))
(defn- native-control! [control]
  (let [state (when (instance? NativeInitBase control)
                (locking native-base-issued (.get native-base-issued control)))]
    (when-not state (fail "Expected issued native Init base operation" {})) state))
(defn- native-progress [data]
  {:phase (:phase data) :guest-steps (:used data 0) :outer-steps (:outer-steps data 0)
   :helper-steps (:helper-steps data 0) :completed-operations (:operations data 0)
   :readiness-queries (:readiness-index data 0) :host-work (:host-work data 0)
   :native-module-count (get-in data [:coverage :query-count]) :source-receipts 0})
(defn- native-failed! [state cause]
  (if-let [failure (:failure @state)] (throw failure)
    (let [child (ex-data cause)]
      (when (:checkpoint child) (swap! state assoc :world (:checkpoint child)))
      (when (:checkpoint-session child) (swap! state assoc :session (:checkpoint-session child)))
      (when-let [{:keys [world bound category]} (:guest-entry @state)]
        (let [known (cond (contains? child :checkpoint) (:checkpoint child)
                          (:guest-returned? @state) (:world @state))
              delta (when (get-in known [:stats :steps])
                      (- (get-in known [:stats :steps]) (get-in world [:stats :steps])))
              returned? (:guest-returned? @state)
              helper (if (and returned? (= :helper-steps category)) (get-in @state [:event :helper-steps] 0) 0)
              charge (when (and (integer? delta) (integer? helper)) (max delta helper))]
          (when (and (integer? delta) (<= 0 delta bound) (integer? helper) (<= 0 helper bound)
                     (integer? charge) (<= 0 charge bound))
            ;; A thrown backend call publishes only a lower-bound checkpoint:
            ;; later instructions may have run without returning a new packet.
            ;; Charge observed work, retaining the unknown residual reservation.
            (swap! state #(-> % (update :used +' charge) (update category +' charge)
                              (assoc :reserved (if returned? 0 (- bound charge))
                                     :failed-guest-observed-steps charge)
                              (dissoc :guest-returned?))))))
      (let [data @state
            failure (ex-info "Native Init base operation failed"
                      (merge child {:checkpoint (:world data) :checkpoint-session (:session data)
                                    :native-init-base-state data :native-init-base-terminal? true}) cause)]
        (swap! state assoc :phase :failed :failure-phase (:phase data) :failure failure)
        (throw failure)))))
(defn- native-own! [state label operation]
  (let [[world value] (operation (:world @state))]
    (swap! state #(-> % (assoc :world world) (assoc-in [:native-owners label] {:value value :state :owned})))
    value))
(defn- native-transfer! [state labels]
  (doseq [label labels]
    (when-not (= :owned (get-in @state [:native-owners label :state]))
      (fail "Native base owner was already consumed" {})))
  (swap! state #(reduce (fn [s label] (assoc-in s [:native-owners label :state] :transferred)) % labels)))
(defn- native-release! [state label]
  (let [{:keys [value] status :state} (get-in @state [:native-owners label])]
    (when-not (= :owned status) (fail "Native base owner is not releasable" {}))
    (let [world (m/release (:world @state) value 1)
          world (if (= value (:result world)) (assoc world :result 0) world)]
      (swap! state #(-> % (assoc :world world) (assoc-in [:native-owners label :state] :released))))))
(defn- native-current! [data]
  (let [{:keys [world session configuration prefix-cap profile readiness coverage]} data
        issued (capability! prefix-cap)
        _ (continuation-readiness! data)
        _ (when-not (identical? (:profile-data data) (graph-profile! profile))
            (fail "Native base lost its exact graph profile" {}))
        _ (graph-installer-matches! (:profile-data data) configuration)
        _ (eval/validate-executables! world (:trusted-functions configuration) source-graph-roots)
        prefix (:prefix issued)
        binding (get-in session [:bindings "lean_run_mod_init_core"])
        actual (native-factory/native-init-coverage readiness (:source prefix) binding)
        modules (mapv :module (:modules prefix))]
    (when-not (and (identical? configuration (:configuration issued))
                   (= coverage actual) (= (count modules) (:query-count actual))
                   (= (set modules) (set (:modules actual)))
                   (every? #(= "all" (:irPhases %)) (:modules prefix)))
      (fail "Native readiness does not cover the exact effective native prefix" {}))
    issued))
(defn- native-requests! [state invoke]
  (let [requests source/init-requests
        names (mapv #(name/from-string (imports/module-string (:module %))) requests)
        [world array] (encoding/encode-names (:world @state) invoke names)
        _ (swap! state #(-> % (assoc :world world) (assoc-in [:native-owners :encoded-names] {:value array :state :owned})))
        refs (proof-array! world array 2)
        _ (when-not (= 2 (count refs)) (fail "Native Init request Name encoding differs" {}))
        values (mapv
                 (fn [i request]
                   (let [label [:request-name i] name-ref (nth refs i)
                         _ (native-own! state label #(vector (m/retain % name-ref 1) name-ref))
                         value (native-own! state [:request i]
                                 #(m/scalar-constructor % 0 [name-ref] {:objects 1 :usize 0 :ssize 3}))
                         _ (native-transfer! state [label])
                         node (reduce (fn [node [offset flag]]
                                        (m/write-scalar-node node {:index 1 :offset offset :type "uint8" :region :scalar}
                                                             (if flag 1 0)))
                                      (m/node (:world @state) value)
                                      (map-indexed vector (map request [:importAll :isExported :isMeta])))]
                     (swap! state update :world m/replace-node value node) value)) (range) requests)
        imports (native-own! state :assembly-imports #(m/allocate % :array 246 values))]
    (native-transfer! state [[:request 0] [:request 1]])
    (native-release! state :encoded-names)
    imports))
(defn- native-attribution-arrays!
  "Preflight the actual native selection used by Lean's finalizeImport:
   constNames from main/private data and extraConstNames from selected IR data.
   Count RAW selected entries before Name projection/deduplication plus the SAME
   request/module occurrence overhead as native graph-plan-selection. Other
   public/server views do not contribute. No guest calls or owner changes."
  [world prefix p]
  (let [native (graph-native-arrays world prefix (:graph-limits p))
        name-count (graph-selected-name-count native [] (count source/init-requests))]
    (when (> name-count (get-in p [:graph-limits :max-names]))
      (fail "Native attribution aggregate names exceed bound" {}))
    {:total (reduce +' 0 (map #(+' (count (:names %)) (count (:extras %))) native))
     :name-count name-count
     :arrays (mapv (fn [index {:keys [names extras]}] [index [names extras]]) (range) native)}))

(defn prepare-native-init-base
  "Prepare one fixed native-only Init reset from an accumulated persistent World.
   REQUEST must already contain immutable :text (no path IO here); its actual
   bounded header must contain only implicit Init/meta Init. READINESS
   comes from the separately opted-in authenticated factory's actual binding.
   Selected native data layout and raw aggregate name count are preflighted
   before guest work and checked again at finish. No query/finalizer executes
   here; no source receipt can be issued by this API."
  [context request prefix profile readiness {:keys [kernel-policy budgets] :as options}]
  (locking context
    (let [state (atom {:native-operation? true :phase :entry :used 0 :reserved 0
                       :outer-steps 0 :helper-steps 0 :operations 0 :host-work 0 :readiness-index 0
                       :native-owners {}})]
      (try
        (when-not (and (map? options) (= 2 (count options)) (= #{:kernel-policy :budgets} (set (keys options))))
          (fail "Native Init base requires explicit policy and budgets only" {}))
        (import-policy! kernel-policy) (import-budgets! budgets)
        (let [entry (resident/snapshot context)
              _ (swap! state assoc :entry entry :world (:world entry) :session (:session entry))
              issued (graph-readiness! entry prefix profile)
              raw-prefix (:prefix issued) p (:graph-profile issued)
              ;; Refuse invalid selected data or an insufficient explicit graph
              ;; budget BEFORE header inspection/Name encoding/readiness/guest work.
              _ (native-attribution-arrays! (:world entry) raw-prefix p)
              binding (get-in entry [:session :bindings "lean_run_mod_init_core"])
              coverage (native-factory/native-init-coverage readiness (:source raw-prefix) binding)
              _ (when-not (and (map? request) (string? (:text request)) (not (contains? request :path))
                               (string? (:file-name request)))
                  (fail "Native Init base requires captured immutable text and file name" {}))
              _ (graph-utf8-size! (:text request) (get-in p [:limits :max-bytes]))
              _ (graph-utf8-size! (:file-name request) (get-in p [:graph-limits :max-key-bytes]))
              captured (graph-capture-request! request p)
              _ (swap! state assoc :prefix-cap prefix :prefix raw-prefix :profile profile :profile-data p
                       :readiness readiness :coverage coverage :certificate (:certificate issued)
                       :configuration (:configuration issued) :native-bindings (:native-bindings issued)
                       :kernel-policy kernel-policy :budgets budgets :request captured :phase :header-started)
              _ (native-current! @state)
              invoke (graph-invocation state (select-keys budgets [:helper-fuel :attempt-fuel]))
              header (graph-inspect-header! state invoke captured p source/init-requests)
              _ (swap! state assoc :header header :phase :assembly-started)
              imports (native-requests! state invoke)
              retained (native-own! state :assembly-state #(vector (m/retain % (:state raw-prefix) 1) (:state raw-prefix)))
              _ (swap! state assoc :assembly {:state retained :imports imports} :phase :readiness)
              control (NativeInitBase.)]
          (locking native-base-issued (.put native-base-issued control state))
          {:control control :progress (native-progress @state)})
        (catch Throwable cause (native-failed! state cause))))))
(def ^:private native-control-fields [:body :locals :joins :frames :status :result :resume-var :host-request :initializing? :initialization-scope])
(defn- native-query! [state]
  (let [data @state
        {:keys [world session coverage readiness readiness-index]} data
        binding (get-in session [:bindings "lean_run_mod_init_core"])
        units (:host-units-per-query coverage)
        next-work (+' (:host-work data) units)]
    (when-not (<= next-work (:max-host-work coverage)) (fail "Native readiness host-work budget exhausted" {}))
    (when-not (and (= :done (:status world)) (empty? (:frames world)) (nil? (:host-request world))
                   (not (:initializing? world)) (not (:initialization-scope world)))
      (fail "Native readiness requires an idle packet" {}))
    (when-let [guards (:readiness-guards data)]
      (when-not (identical? guards (:initialized-modules world))
        (fail "Native readiness guards changed within its query phase" {})))
    ;; Reserve HOST work before dispatch. No guest instruction/fuel reservation
    ;; is charged for this fixed host capability invocation.
    (swap! state assoc :host-work next-work :readiness-guards (:initialized-modules world))
    (let [pair (native-factory/query-native-init readiness world binding readiness-index)
          _ (swap! state assoc :readiness-returned pair)
          _ (when-not (and (vector? pair) (= 2 (count pair))) (fail "Native query returned another packet shape" {}))
          [after value] pair
          _ (swap! state #(-> % (assoc :world after)
                              (assoc-in [:native-owners :readiness-result] {:value value :state :owned})))
          node (when (m/ref? value) (m/node after value))]
      (when-not (and (identical? (:functions world) (:functions after))
                     (identical? (:globals world) (:globals after))
                     (identical? (:native-imports world) (:native-imports after))
                     (identical? (:initialized-modules world) (:initialized-modules after))
                     (every? #(identical? (get world %) (get after %)) native-control-fields)
                     (= (get-in world [:stats :steps]) (get-in after [:stats :steps]))
                     (m/ref? value) (not (m/native-reference? after value))
                     (not (contains? (:heap world) (:id value)))
                     (= :ctor (:kind node)) (= 0 (:tag node)) (bridge/constructor-layout? node 1 0)
                     (= [1] (:fields node)) (= 1 (:rc node)))
        (fail "Native query must return actual owned IO.ok true without changing execution state" {}))
      (native-release! state :readiness-result)
      (swap! state #(-> % (update :readiness-index inc) (update :operations inc)
                        (dissoc :readiness-returned)))
      (when (= (:readiness-index @state) (:query-count coverage))
        (swap! state assoc :phase :assembled :readiness-world (:world @state) :readiness-session session)))))
(defn advance-native-init-base!
  "Bounded one-shot native readiness/finalizer continuation. Host query work and
   guest helper/outer work have separate ledgers; observers run after escrow."
  [control {:keys [max-operations wall-ms observe!] :as limits}]
  (let [state (native-control! control)]
    (locking control
      (when-let [failure (:failure @state)] (throw failure))
      (when-not (and (not (:busy? @state)) (contains? #{:readiness :assembled :running} (:phase @state)))
        (fail "Native base control is not advanceable" {}))
      (swap! state assoc :busy? true)
      (try
        (when-not (and (map? limits) (<= 2 (count limits) 3)
                       (every? #{:max-operations :wall-ms :observe!} (keys limits))
                       (contains? limits :max-operations) (contains? limits :wall-ms)
                       (or (nil? observe!) (fn? observe!))) (fail "Native base requires explicit slice limits" {}))
        (positive-long! max-operations :max-operations) (positive-long! wall-ms :wall-ms)
        (let [started (System/nanoTime)]
          ;; Full code/coverage checks once per slice. Between readiness calls
          ;; only the fixed nonreentrant binding executes; its returned packet
          ;; must preserve exact control/functions/Source/guard identities.
          (native-current! @state)
          (loop [n 0]
            (when (not= :readiness (:phase @state)) (native-current! @state))
            (when (and (not= :io-completed (:phase @state)) (< n max-operations)
                       (< (/ (- (System/nanoTime) started) 1000000.0) wall-ms))
              (if (= :readiness (:phase @state))
                (native-query! state)
                (let [{:keys [world session budgets event assembly]} @state
                      boundary? (= :boundary (:status event))
                      bound (get budgets (if boundary? :helper-fuel :outer-fuel))]
                  (when (> bound (- (:attempt-fuel budgets) (:used @state)))
                    (fail "Native finalizer cannot reserve next guest operation" {}))
                  (swap! state assoc :reserved bound :guest-entry {:world world :bound bound
                                                                  :category (if boundary? :helper-steps :outer-steps)}
                         :guest-returned? false)
                  (when (= :assembled (:phase @state))
                    (when-not (and (identical? world (:readiness-world @state))
                                   (identical? session (:readiness-session @state))
                                   (= (:readiness-index @state) (get-in @state [:coverage :query-count]))
                                   (identical? (:readiness-guards @state) (:initialized-modules world)))
                      (fail "Native finalizer lost its actual full-readiness packet" {}))
                    (swap! state assoc :phase :running :finalizer-started? true)
                    (native-transfer! state [:assembly-state :assembly-imports])
                    (swap! state assoc :world (m/start world (:finalize source/helpers)
                                               [(:state assembly) (:imports assembly) (get-in @state [:entry :options]) m/erased])))
                  (let [before (:world @state)
                        event (if boundary?
                                (raw/complete-host-boundary (:token event) {:helper-fuel (:helper-fuel budgets)})
                                (raw/advance-to-boundary (assoc (:session @state) :fuel (:outer-fuel budgets)) before))
                        _ (swap! state assoc :event event :world (:state event) :session (:session event) :guest-returned? true)
                        delta (- (get-in event [:state :stats :steps]) (get-in before [:stats :steps]))
                        helper (:helper-steps event 0) charge (if boundary? (max delta helper) delta)]
                    (when-not (and (integer? delta) (<= 0 delta bound)
                                   (integer? helper) (<= 0 helper bound)
                                   (<= charge (- (:attempt-fuel budgets) (:used @state))))
                      (fail "Native finalizer observed invalid guest charge" {}))
                    (swap! state #(-> % (update :used +' charge) (update :operations inc)
                                      (update (if boundary? :helper-steps :outer-steps) +' charge)
                                      (assoc :reserved 0) (dissoc :guest-entry :guest-returned?)))
                    (case (:status event)
                      :done (swap! state #(-> % (assoc :phase :io-completed :io (:value event))
                                               (assoc-in [:native-owners :finalizer-io] {:value (:value event) :state :owned})))
                      (:handler-completed :boundary :paused) nil
                      (fail "Unexpected native finalizer event" {})))))
              (when observe! (observe! (native-progress @state)))
              (recur (inc n)))))
        {:progress (native-progress @state)}
        (catch Throwable cause (native-failed! state cause))
        (finally (swap! state assoc :busy? false))))))
(defn- native-attribution! [state invoke prefix p environment selection]
  ;; Repeat actual-World validation after finalization; do not trust preflight.
  (let [arrays (native-attribution-arrays! (:world @state) prefix p)
        seen (volatile! {}) total-name-bytes (volatile! 0)]
    (doseq [[index arrays] (:arrays arrays) names arrays reference names]
      (let [wire (graph-wire-name!
                   (structured-name-value
                     (bridge/project-name-bounded (:world @state) reference (get-in p [:limits :name-limits])))
                   false (:graph-limits p) total-name-bytes)
            expected (get-in selection [:plan :name-attribution wire :module-index])]
        ;; Pinned Lean const2ModIdx.insertIfNew and G0 agree: authenticated
        ;; native aliases/subsumption keep their FIRST module, unlike local
        ;; source conflicts. Validate only the first selected occurrence.
        (when-not (contains? @seen wire)
          (when-not (= index expected)
            (fail "Native attribution selection differs from actual selected data" {}))
          (vswap! seen assoc wire index)
          (let [[world result] (invoke (:world @state) module-index-helper [environment reference])
                _ (swap! state #(-> % (assoc :world world)
                                    (assoc-in [:native-owners :attribution-result] {:value result :state :owned})))
                node (when (m/ref? result) (m/node world result))]
            (when-not (and (= 1 (:tag node)) (bridge/constructor-layout? node 1 0)
                           (= expected (native/nat-value {:ref? m/ref? :node m/node} world (first (:fields node)))))
              (fail "Native finalizer has another const/extra module attribution" {}))
            (native-release! state :attribution-result)
            (swap! state update :native-attributions (fnil inc 0))))))))
(defn finish-native-init-base!
  "Consume actual native finalizer IO, freshly check exact native CI/header/order,
   and adopt its real new Environment. Never issue a source/graph receipt."
  [control]
  (let [state (native-control! control)]
    (locking control
      (when-let [failure (:failure @state)] (throw failure))
      (when-not (and (not (:busy? @state)) (= :io-completed (:phase @state)))
        (fail "Native base has no completed unconsumed IO" {}))
      (swap! state assoc :busy? true :phase :checking-started)
      (try
        (native-current! @state)
        (let [{:keys [world io prefix certificate profile-data kernel-policy budgets entry configuration]} @state
              invoke (graph-invocation state (select-keys budgets [:helper-fuel :attempt-fuel]))
              _ (swap! state assoc-in [:native-owners :finalizer-io :state] :completion-attempted)
              finished (imports/finish-finalization world io invoke
                         {:kernel-policy (assoc kernel-policy :projection-certificate certificate)
                          :finalizer-attestation {:requested-imports source/init-requests :header-helper (:header source/helpers)}})
              _ (swap! state assoc :finished finished :world (:world finished))
              _ (when-not (= :ok (:status finished)) (fail "Native finalizer returned IO error" {}))
              _ (swap! state #(-> % (assoc-in [:native-owners :finalizer-io :state] :consumed)
                                   (assoc-in [:native-owners :final-environment] {:value (:environment finished) :state :owned})))
              selection (graph-plan-selection! (:world @state) prefix profile-data [] [])
              observed (graph-observe-checked-union! (:world @state) invoke (:environment finished)
                                                   prefix certificate profile-data selection false)
              _ (swap! state assoc :world (:world observed) :native-observation observed)
              _ (when-not (and (= (:constants certificate) (get-in finished [:certificate :constants]))
                               (identical? (:checked-env observed) (get-in finished [:certificate :env])))
                  (fail "Native finalizer certificate differs from exact observed native union" {}))
              _ (native-attribution! state invoke prefix profile-data (:environment finished) selection)
              _ (doseq [field [:source-modules :source-regions :source-import-prefixes :source-import-receipts]]
                  (when-not (identical? (get-in entry [:world field]) (get-in @state [:world field]))
                    (fail "Native base changed an accumulated source registry" {:registry field})))
              _ (preserve-admission-baseline! (:world entry) (:world @state) (:limits profile-data))
              _ (let [before (get-in entry [:world :globals]) after (get-in @state [:world :globals])]
                  (when-not (and (map? before) (map? after)
                                 (<= (+' (count before) (count after)) (get-in profile-data [:limits :max-declarations])))
                    (fail "Native base globals exceed aggregate preservation bound" {}))
                  ;; Finalization may initialize NEW pure lazy cache entries;
                  ;; it must preserve every preexisting native/source cache.
                  (doseq [[name value] before]
                    (when-not (and (contains? after name) (identical? value (get after name)))
                      (fail "Native base replaced an existing global cache entry" {}))))
              _ (doseq [field [:initialized-modules :initializing? :initialization-scope :native-imports]]
                  (when-not (identical? (get-in entry [:world field]) (get-in @state [:world field]))
                    (fail "Native base changed native/global initialization state" {:field field})))
              _ (swap! state update :world m/release (:environment entry) 1)
              _ (swap! state assoc-in [:native-owners :prior-environment] {:value (:environment entry) :state :released})
              prepared (assoc (packet entry (:world @state) (assoc (:session @state) :fuel (get-in entry [:session :fuel])))
                              :environment (:environment finished))
              _ (swap! state assoc :adoption-entry prepared)
              context (resident/adopt-prepared prepared configuration)
              _ (swap! state assoc :adopted-context context)
              completed {:phase :finished :used (:used @state) :helper-steps (:helper-steps @state)
                         :outer-steps (:outer-steps @state) :operations (:operations @state)
                         :readiness-index (:readiness-index @state) :host-work (:host-work @state)
                         :coverage (select-keys (:coverage @state) [:query-count]) :busy? true}
              result {:context context :request (:request @state) :header (:header @state)
                      :native-base {:module-count (get-in @state [:coverage :query-count])
                                    :constant-count (count (:constants observed)) :source-receipts 0}
                      :progress (native-progress completed)}]
          (reset! state completed) result)
        (catch Throwable cause (native-failed! state cause))
        (finally (swap! state assoc :busy? false))))))


(defn- dispose-staged-operation! [control state graph-mode?]
  (locking control
    (let [data @state]
      (when (:busy? data) (fail "Cannot dispose a busy resident operation" {}))
      (when (and (some? graph-mode?)
                 (not= graph-mode? (boolean (:graph-operation? data))))
        (fail "Import operation belongs to another fixed API" {}))
      (if (= :disposed (:phase data))
        (:disposal data)
        (let [receipt {:phase :disposed :previous-phase (:phase data)
                       :borrowed-source-closed false :guest-replayed false}
              tombstone {:phase :disposed :busy? false :disposal receipt
                         :graph-operation? (boolean (:graph-operation? data))}
              claimed (assoc data :busy? true :dispose-state :running)]
          ;; Construct both small objects before claim/effects. Whole-branch
          ;; abandonment never guesses ownership at a lower-bound checkpoint.
          ;; Finished controls already transferred their Context and hold none.
          (reset! state claimed)
          (try
            (when-let [token (get-in data [:event :token])]
              (raw/abandon-host-boundary! token))
            (when-let [context (:adopted-context data)]
              (resident/abandon! context))
            (reset! state tombstone)
            receipt
            (catch Throwable disposal-cause
              ;; No success claim and no canonical operation error replacement.
              ;; Retain exact pending owner state for explicit diagnosis.
              (try (swap! state assoc :disposal-failure disposal-cause :dispose-state :failed)
                   (catch Throwable _))
              ;; Busy remains terminal after a disposal failure: no implicit
              ;; operation/disposal retry or allocation masking in finally.
              (throw disposal-cause))))))))
(defn dispose-import!
  "Abandon only this issued legacy import branch; no guest replay/Source close.
   Busy or foreign-mode controls reject. Successful returned Contexts stay live."
  [control]
  (dispose-staged-operation! control (import-control! control) false))
(defn dispose-source-graph-import!
  "Abandon only this issued graph import branch, preserving prior host effects.
   Caller-retained exceptions/snapshots remain caller-owned diagnostic roots."
  [control]
  (dispose-staged-operation! control (import-control! control) true))
(defn dispose-native-init-base!
  "Abandon only this issued native-reset branch; never run its finalizer/handler.
   Borrowed Source/Store/lease and successful returned Context remain external."
  [control]
  (dispose-staged-operation! control (native-control! control) nil))
