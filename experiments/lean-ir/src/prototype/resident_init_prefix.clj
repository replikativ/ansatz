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
            [prototype.resident-import :as standalone]
            [ansatz.kernel.name :as name]
            [clojure.string :as str])
  (:import [ansatz.kernel Env ConstantInfo]
           [java.util WeakHashMap]))

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
    (:reconstruction data) (assoc :reconstruction (get-in data [:reconstruction :audit]))))
(defn- import-failure! [state cause]
  (let [data @state previous (:phase data)
        wrapped (ex-info (or (.getMessage cause) "Resident Init import failed")
             (merge {:checkpoint (:world data) :checkpoint-session (:session data)} (ex-data cause)
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
                     :resident-init-import-terminal? true}) cause)]
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

(defn- continuation-readiness! [{:keys [world session prefix certificate configuration]}]
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
  true)

(declare in-reconstruction-scope release-reconstruction-owners)

(defn advance-import!
  "Advance an issued operation in bounded cooperative slices. LIMITS is exactly
   {:max-operations positive :wall-ms positive}, optionally :observe! scalar-fn.
   Wall budget is checked BETWEEN operations, never preempts host/native work.
   Reserve the full next outer/helper bound from the immutable aggregate attempt
   budget before running. Completed events are escrowed before accounting and
   observers; any failure poisons the operation permanently. No caller snapshot,
   budget replacement, retry or finalizer replay is accepted."
  [control {:keys [max-operations wall-ms observe!] :as limits}]
  (let [state (import-control! control)]
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

(defn finish-import!
  "Consume this operation's completed genuine finalizer IO exactly once. Freshly
   check the WHOLE Init+A map; only immutable native projections may reuse the
   privately retained original certificate. Return new :context, captured :request,
   actual :header and descriptive A-only :import-receipt. No caller certificate,
   finalizer invocation, initializer replay or borrowed lease closure occurs here."
  [control]
  (let [state (import-control! control)]
    (locking control
      (when-let [failure (:failure @state)] (throw failure))
      (when-not (and (not (:busy? @state)) (= :io-completed (:phase @state)))
        (fail "Init import has no unconsumed completed finalizer IO" {:phase (:phase @state)}))
      ;; Claim the IO before any helper/checking effect. Later errors cannot retry.
      (swap! state assoc :phase :checking-started :busy? true)
      (try
        (continuation-readiness! @state)
        (let [{:keys [assembly world io certificate kernel-policy budgets configuration entry]} @state
              invoke (fn [world target args]
                       (swap! state assoc :world world)
                       (let [called (raw/call (assoc (:session @state) :fuel (:helper-fuel budgets)) world target args)]
                         (swap! state assoc :world (:state called) :session (:session called)
                                :last-call {:target target :arguments args :returned called})
                         [(:state called) (:value called)]))
              finished (source/finish-over-init assembly world io invoke
                         {:kernel-policy (assoc kernel-policy :projection-certificate certificate)})]
          (swap! state assoc :finished finished :world (:world finished))
          (when-not (= :ok (:status finished))
            (fail "Init source finalizer returned IO error" {:checkpoint (:world finished) :io-result (:io-result finished)}))
          (swap! state update :owners assoc :final-environment (:environment finished)
                 :final-environment-state :owned :assembly-owner-state :consumed-by-successful-finalizer)
          (let [receipt (:source-import-receipt finished)]
            (when-not (and receipt (identical? (:checked-env receipt) (get-in finished [:certificate :env])))
              (fail "Init import has no exact fresh source-only checked receipt" {}))
            (release-reconstruction-owners state)
            (swap! state assoc :phase :adopt-started)
            (swap! state update :world m/release (:module-name @state) 1)
            (swap! state update :owners assoc :module-name-state :released)
            (swap! state update :world m/release (:environment entry) 1)
            (swap! state update :owners assoc :prior-environment-in-new-branch :released)
            (let [prepared (assoc (packet entry (:world @state)
                                               (assoc (:session @state) :fuel (get-in entry [:session :fuel])))
                                 :environment (:environment finished))
                  _ (swap! state assoc :adoption-entry prepared)
                  context (resident/adopt-prepared prepared configuration)]
              (swap! state assoc :phase :finished)
              {:context context :request (:request @state) :header (:header @state)
               :import-receipt {:module (:module @state) :unit-digest (:unit-digest receipt)
                                :constant-count (count (:constants receipt))}})))
        (catch Throwable cause (import-failure! state cause))
        (finally (swap! state assoc :busy? false))))))


;; Pure original-publication provenance groundwork. This does not issue a
;; capability, associate a target, or authorize reconstruction execution.
(defn- proof-array! [world value maximum]
  (let [node (when (m/ref? value) (m/node world value))]
    (when-not (and (= :array (:kind node)) (vector? (:fields node))
                   (<= (count (:fields node)) maximum))
      (fail "Publication proof requires a bounded guest array" {:maximum maximum}))
    (:fields node)))

(defn- publication-proof!
  [original prefix certificate module invoke {:keys [max-constants name-limits] :as limits}]
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
            _ (when-not (and (= :over-init (:profile entry)) (= module (:module entry))
                             (= environment (:environment entry))
                             (identical? unit (get-in world [:eval-const-authorizations :units digest]))
                             (= [] (:actions unit)) (= [] (get-in unit [:manifest :initializationPlan :actions]))
                             (= module (get-in unit [:manifest :initializationPlan :module]))
                             (= source/init-requests (get-in entry [:metadata :imports]))
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
                                 (when (or (contains? out name) (contains? (:constants certificate) name)
                                           (not (m/ref? value))
                                           (not= name (imported/project-constant-name world value name-limits)))
                                   (fail "Source publication duplicate, collision or name/ref mismatch" {}))
                                 (assoc out name value))) {} (map vector names values))
            guest-names (reduce (fn [out value]
                                  (let [name (bridge/project-name-bounded world value name-limits)]
                                    (when (or (contains? out name) (contains? (:constants certificate) name))
                                      (fail "Source publication duplicate/colliding constant/extra name" {}))
                                    (assoc out name value))) {} (concat names extras))
            expected (merge (:constants certificate) exported)
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
            _ (doseq [[name ci] (:projected certificate)]
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
