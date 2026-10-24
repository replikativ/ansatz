(ns prototype.compact-import-check
  "Definitions-only, one-shot consumer of a completed/restored guest finalizer IO.
   Explicit compact projection consumer over an unchanged source-bound runtime.
   No restore, bootstrap, finalizer, source acquisition, or resource close runs here.
   Caller supplies independent trusted preparation and keeps every source lease alive."
  (:require [prototype.machine :as m]
            [prototype.eval-const :as eval]
            [prototype.raw-interop :as raw]
            [prototype.module-import :as imports]
            [prototype.imported-kernel :as kernel]
            [prototype.kernel-bridge :as bridge]
            [prototype.compact-kernel-projection :as compact]
            [ansatz.kernel.env :as env]
            [clojure.set :as set])
  (:import [ansatz.kernel ConstantInfo Env TypeChecker]))

(deftype Check [state])
(defn- fail [message data] (throw (ex-info message data)))
(defn- state-of [control]
  (when-not (instance? Check control) (fail "Expected restored import check" {}))
  (.-state ^Check control))
(defn checkpoint
  "Borrow exact entry/result/progress/failure packets. Never print or serialize this map.
   Snapshot aliases are diagnostic alternatives, not additional guest owners."
  [control] @(state-of control))

(defn- ready! [{:keys [world session io-result]} configuration]
  (when-not (and (map? world) (map? session)
                 (map? (:functions world))
                 (identical? (:functions world) (:functions session))
                 (= :done (:status world)) (empty? (:frames world))
                 (nil? (:host-request world)) (empty? (:kernel-environments world))
                 (m/ref? io-result) (= io-result (:result world)))
    (fail "Strict restored checking requires idle matching precheck world/session/IO" {}))
  (let [node (m/node world io-result)]
    (when-not (and (= :ctor (:kind node)) (contains? #{0 1} (:tag node))
                   (= 1 (count (:fields node)))
                   (integer? (:rc node)) (<= 0 (:rc node)))
      (fail "Expected a live owned guest finalizer IO.Result" {})))
  (when-not (and (map? configuration)
                 (every? #{:trusted-functions :trusted-bindings :kernel-helpers :kernel-policy
                           :fuel :observe!} (keys configuration))
                 (map? (:trusted-functions configuration))
                 (map? (:trusted-bindings configuration))
                 (map? (:kernel-helpers configuration))
                 (map? (:kernel-policy configuration))
                 (integer? (:fuel configuration)) (<= 1 (:fuel configuration) Long/MAX_VALUE)
                 (or (not (contains? configuration :observe!)) (fn? (:observe! configuration))))
    (fail "Explicit independent strict-check registries/helpers/policy and fuel required" {}))
  (when-not (= (set (keys (:trusted-bindings configuration)))
               (set (keys (:bindings session))))
    (fail "Strict restored check binding registry changed" {}))
  (doseq [[symbol binding] (:trusted-bindings configuration)]
    (when-not (identical? binding (get-in session [:bindings symbol]))
      (fail "Strict restored check host capability changed" {:symbol symbol})))
  ;; finish-finalization merges these defaults. Validate exactly the roots it will call,
  ;; including an inherited default omitted from the explicit override map.
  (let [helpers (merge imports/helpers (:kernel-helpers configuration))
        roots (mapv helpers [:constants :root :constant-map :quot-init?])]
    (when-not (every? vector? roots) (fail "Missing selected strict kernel helper" {}))
    (eval/validate-executables! world (:trusted-functions configuration) roots)
    helpers))

(defn prepare
  "Prepare a per-operation check, without guest execution or ownership transfer.
   CANDIDATE is {:world :session :io-result} from the actual completed finalizer or
   authenticated checkpoint reader. This function does not authenticate an archive
   or establish finalizer provenance. Phase flags/certificates are not authority.

   CONFIGURATION requires independently retained :trusted-functions/:trusted-bindings,
   :kernel-helpers, explicit :kernel-policy and positive :fuel PER raw invocation.
   Optional :observe! receives scalars only, after returned owners have been escrowed."
  [candidate configuration]
  (let [entry (select-keys candidate [:world :session :io-result])
        helpers (ready! entry configuration)]
    (Check. (atom {:phase :ready :entry entry :configuration configuration :helpers helpers}))))

(defn summary [control]
  (let [{:keys [phase result failure]} (checkpoint control)
        message (some-> failure .getMessage)]
    {:verification-progress (:verification-progress (checkpoint control))
     :phase phase :checking-completed (= :ok (:status result))
     :guest-io-error (= :io-error (:status result))
     :constants (count (get-in result [:certificate :constants]))
     :failure-message (when message (subs message 0 (min 700 (count message))))}))

;; Read-only adapters to pinned implementation details, not Var replacement.
;; A future public verifier API should replace these adapters after compatibility validation.
(defn- checking-plan [entries names]
  ;; Match the ordinary verifier: build-only graph containers die in its helper
  ;; frame before admission; retain only borrowed members and scheduling data.
  (#'kernel/checking-plan (#'kernel/groups entries) names))
(defn- immutable-projection-sources [world] (#'kernel/immutable-projection-sources world))
(defn- validate-quot-bootstrap [checked] (#'kernel/validate-quot-bootstrap checked))
(defn- array! [world value] (#'imports/array! world value))
(def ^:private helpers imports/helpers)
(defn- project-finalizer-flag [world environment invoke targets certificate attestation]
  (#'imports/project-finalizer-flag world environment invoke targets certificate attestation))

(def ^:dynamic ^:private *stage!* (fn [_] nil))
(defn- stage! [record]
  (let [runtime (Runtime/getRuntime)]
    (*stage!* (assoc record :heap-used (- (.totalMemory runtime) (.freeMemory runtime))
                     :time-nanos (System/nanoTime)))))

(defn- project-entries [world values]
  ;; Invocation-local memo dies with this frame, before dependency graphs exist.
  (stage! {:phase :projection :projected-constants 0 :constants-total (count values)})
  (let [project-constant (:project-constant (compact/make-scoped-projector world))]
    (mapv (fn [index guest]
            (let [constant (project-constant world guest)]
              (when (zero? (mod (inc index) 1024))
                (stage! {:phase :projection :projected-constants (inc index)
                         :constants-total (count values)}))
              {:guest guest :constant constant}))
          (range) values)))

(defn verify-constants
  "Fresh strict admission with a compact projector and unchanged pinned checker rules.
   No caller-provided projection certificate is admitted by this consumer."
  ([world values] (verify-constants world values {}))
  ([world values {:keys [allow-axioms? allow-compiler-markers? allow-unsafe? fuel projection-certificate]
                  :or {fuel 20000000}}]
   (when-not (and (integer? fuel) (<= 1 fuel Long/MAX_VALUE)) (fail "Invalid imported checker fuel" {}))
   (when (and projection-certificate
              (not (and (instance? Env (:env projection-certificate))
                        (map? (:constants projection-certificate))
                        (map? (:projected projection-certificate)))))
     (fail "Invalid trusted projection certificate" {}))
   (when projection-certificate (fail "Compact first-pass consumer rejects projection certificates" {}))
   (let [entries (project-entries world values)
         names (map #(.name ^ConstantInfo (:constant %)) entries)]
     (when-not (= (count names) (count (set names))) (fail "Duplicate imported constant; native subsumption is not supported" {}))
     (let [quotients (filter #(.isQuot ^ConstantInfo (:constant %)) entries)]
       (when (and (seq quotients) (not= #{"Quot" "Quot.mk" "Quot.lift" "Quot.ind"}
                                        (set (map #(str (.name ^ConstantInfo (:constant %))) quotients))))
         (fail "Imported quotient bootstrap requires all four canonical primitives" {})))
     (doseq [{:keys [guest ^ConstantInfo constant]} entries]
       (when (and (.isAxiom constant) (not (and allow-compiler-markers? (bridge/compiler-marker-declaration? world guest))) (not allow-axioms?))
         (fail "Imported axiom admission requires explicit host policy" {:name (.name constant)}))
       (when (and (or (.isUnsafe constant) (and (.isDef constant) (not= 0 (.safety constant))))
                  (not (and allow-compiler-markers? (bridge/compiler-marker-declaration? world guest))) (not allow-unsafe?))
         (fail "Imported unsafe/partial admission requires explicit host policy" {:name (.name constant)})))
     (stage! {:phase :dependency-construction :constants (count entries)})
     (let [{:keys [members-by-key dependents degrees ready group-count]}
           (checking-plan entries names)]
         (loop [queue ready cursor 0 degrees degrees ^Env checked (Env.) order []]
           (do
             (when (zero? (mod cursor 1024)) (stage! {:phase :kernel-admission :groups-checked cursor :groups-total group-count}))
             (if (= cursor (count queue))
               (do
                 (when-not (= group-count cursor)
                   (fail "Unsupported recursive imported kernel dependency group"
                         {:remaining (- group-count cursor)}))
                 (let [actual (set (map #(.name ^ConstantInfo %) (.allConstants checked)))]
                   (when-not (= (set names) actual)
                     (fail "Kernel generated constants absent from imported environment" {:extra (set/difference actual (set names))}))
                   {:env checked :projection-sources (immutable-projection-sources world)
                    :constants (into {} (map (fn [{:keys [guest ^ConstantInfo constant]}] [(.name constant) guest])) entries)
                    :projected (into {} (map (fn [{:keys [^ConstantInfo constant]}] [(.name constant) constant])) entries)
                    :order order :axioms (set (map #(.name ^ConstantInfo (:constant %)) (filter #(.isAxiom ^ConstantInfo (:constant %)) entries)))}))
               (let [key (nth queue cursor) members (get members-by-key key)
                     checked (case (first key)
                               :single (let [^ConstantInfo ci (first members)]
                                         (when (.isQuot ci) (validate-quot-bootstrap checked))
                                         (TypeChecker/checkConstant checked ci (long fuel)))
                               :mutual (TypeChecker/checkMutualDefinitions checked members (long fuel))
                               :inductive (let [ind-map (into {} (map #(vector (.name ^ConstantInfo %) %) (filter #(.isInduct ^ConstantInfo %) members)))
                                                inds (mapv ind-map (second key)) first-ind ^ConstantInfo (first inds)]
                                            (env/check-inductive-bundle checked
                                                                        (env/mk-inductive-bundle (vec (.levelParams first-ind)) (.numParams first-ind) (.isUnsafe first-ind)
                                                                                                 inds (filterv #(.isCtor ^ConstantInfo %) members) (filterv #(.isRecursor ^ConstantInfo %) members)) fuel)))
                     [degrees queue] (reduce (fn [[degrees queue] dependent]
                                               (let [degree (dec (get degrees dependent))]
                                                 [(assoc degrees dependent degree) (if (zero? degree) (conj queue dependent) queue)]))
                                             [degrees queue] (get dependents key))]
                 (recur queue (inc cursor) degrees checked (conj order key))))))))))

(defn finish-finalization
  "Consume the owned IO.Result of an actual guest import finalizer and strictly
   associate its final checked map. This also completes a resumed finalizer:
   callers must supply its actual world/result, not reconstruct an Environment.
   Guest errors remain owned in :io-result; success owns :environment.
   Default quotient-state association remains strict. Optional trusted
   :finalizer-attestation {:requested-imports exactHeader :header-helper Name}
   projects the actual private/classic finalizer's !imports.isEmpty quotient
   metadata only AFTER all constants pass strict checking. It adds no primitives.
   Failures preserve a cause's latest checkpoint/session and named owners. The
   original owned IO snapshot is separate under :finalizer-result; the owned
   Environment at checking entry is paired under :finalization-entry. These are
   diagnostic alternatives, never permission to retry effects. The original raw
   session is caller-held; this function cannot reconstruct it from INVOKE."
  ([world result invoke] (finish-finalization world result invoke {}))
  ([world result invoke options]
   (let [targets (merge helpers (:helpers options))
         finalizer-result {:checkpoint world :io-result result}
         node (when (m/ref? result) (m/node world result))]
     (when-not (and (= :ctor (:kind node)) (contains? #{0 1} (:tag node)) (= 1 (count (:fields node))))
       (fail "Malformed guest import IO.Result" {:checkpoint world :io-result result :finalizer-result finalizer-result}))
     (if (= 1 (:tag node))
       {:status :io-error :world world :io-result result}
       (let [environment (first (:fields node))
             _ (when-not (m/ref? environment) (fail "Guest import did not return an Environment reference"
                                                    {:checkpoint world :io-result result :finalizer-result finalizer-result}))
             world (-> world (m/retain environment 1) (m/release result 1) (assoc :result 0))]
         (try
           (let [[world constants] (invoke world (:constants targets) [environment])
                 values (array! world constants)
                 certificate (verify-constants world values (:kernel-policy options))
                 world (m/release world constants 1)
                 [world certificate] (project-finalizer-flag world environment invoke targets certificate
                                                             (:finalizer-attestation options))
                 _ (stage! {:phase :association :constants (count (:constants certificate))})
                 world (kernel/associate-checked {:invoke invoke} world environment targets certificate)]
             {:status :ok :world (assoc world :result 0) :environment environment :certificate certificate})
           (catch Exception cause
             (let [data (ex-data cause) newer? (some? (:checkpoint data))]
               (throw (ex-info "Guest import kernel association failed"
                               (cond-> (merge {:phase :kernel-association} data
                                              {:checkpoint (or (:checkpoint data) world)
                                               :finalizer-result finalizer-result
                                               :finalization-entry {:checkpoint world :environment environment}})
                           ;; A child checkpoint may have consumed or changed
                           ;; this owner. Do not pair an entry-world Env with it.
                                 (not newer?) (assoc :environment environment)
                                 (:checkpoint-session data) (assoc :session (:checkpoint-session data)))
                               cause))))))))))

(defn check!
  "Consume the entry IO in this immutable branch exactly once, strictly checking
   the actual guest map and associating its exact kernel roots. Returns a checked
   packet owning :environment, or :io-error packet owning :io-result, with latest
   :session. No eager second native certificate is constructed.

   Failure is terminal. Child checkpoint/session and paired original entry, latest
   raw progress and any completed result stay available through checkpoint/ex-data.
   Caller must not retry an alternative snapshot to recover external effects."
  [control]
  (let [state (state-of control) before @state]
    (when-not (and (= :ready (:phase before))
                   (compare-and-set! state before (assoc before :phase :checking)))
      (fail "Restored import check already claimed; no retry" {}))
    (let [{:keys [entry configuration helpers]} before
          active (atom (assoc (:session entry) :fuel (:fuel configuration)))
          progress (volatile! nil)]
      (try
        (ready! entry configuration)
        (let [invoke (fn [world target args]
                       (let [started {:phase :entry :world world :session @active
                                      :target target :arguments args}]
                         (vreset! progress started)
                         (swap! state assoc :raw-progress started)
                         (let [returned (raw/call @active world target args)
                               completed {:phase :return :world (:state returned)
                                          :session (:session returned) :target target
                                          :value (:value returned)}]
                           (reset! active (:session returned))
                           (vreset! progress completed)
                           (swap! state assoc :raw-progress completed)
                           [(:state returned) (:value returned)])))
              result (assoc (binding [*stage!* #(swap! state assoc :verification-progress %)]
                              (finish-finalization (:world entry) (:io-result entry) invoke
                                                   {:helpers helpers :kernel-policy (:kernel-policy configuration)}))
                            :session @active)]
          ;; Save the exact returned owner/certificate/session BEFORE assertions or observation.
          (swap! state assoc :result result)
          (when-not (contains? #{:ok :io-error} (:status result))
            (fail "Strict checking returned an unexpected status" {}))
          (when-let [observe! (:observe! configuration)] (observe! (summary control)))
          (swap! state assoc :phase (if (= :ok (:status result)) :checked :guest-io-error))
          result)
        (catch Throwable cause
          (let [data (ex-data cause)
                ;; A failed helper can have a newer session than its last successful sibling.
                ;; Keep the child's precise checkpoint/session; progress is separate evidence.
                failure (ex-info (or (.getMessage cause) "Restored import checking failed")
                                 (merge data {:restored-check-entry entry
                                              :restored-check-progress @progress
                                              :restored-check-result (:result @state)}) cause)]
            (swap! state assoc :phase :failed :failure failure)
            (throw failure)))))))
