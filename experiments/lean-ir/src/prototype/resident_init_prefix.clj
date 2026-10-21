(ns prototype.resident-init-prefix
  "Optional checked-Init prefix preparation and staged over-Init source imports.
   The original successful CHECKED result is a TRUSTED host input. Issuing an
   opaque prefix does not authenticate the provenance of a caller-created map.
   Context branches own guest roots; native Stores and catalogues stay borrowed."
  (:require [prototype.resident-frontend :as resident]
            [prototype.source-import :as source]
            [prototype.module-import :as imports]
            [prototype.module-store :as store]
            [prototype.eval-const :as eval]
            [prototype.raw-interop :as raw]
            [prototype.machine :as m]
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
  {:phase (:phase data) :guest-steps (:used data 0)
   :outer-steps (:outer-steps data 0) :helper-steps (:helper-steps data 0)
   :completed-operations (:operations data 0)})
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
                        next-event (if boundary?
                                     (raw/complete-host-boundary (:token event) {:helper-fuel (:helper-fuel budgets)})
                                     (raw/advance-to-boundary session before))]
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
