(ns prototype.restored-import-check
  "Definitions-only, one-shot consumer of a completed/restored guest finalizer IO.
   No restore, bootstrap, finalizer, source acquisition, or resource close runs here.
   Caller supplies independent trusted preparation and keeps every source lease alive."
  (:require [prototype.machine :as m]
            [prototype.eval-const :as eval]
            [prototype.raw-interop :as raw]
            [prototype.module-import :as imports]))

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
    {:phase phase :checking-completed (= :ok (:status result))
     :guest-io-error (= :io-error (:status result))
     :constants (count (get-in result [:certificate :constants]))
     :failure-message (when message (subs message 0 (min 700 (count message))))}))

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
              result (assoc (imports/finish-finalization (:world entry) (:io-result entry) invoke
                                                         {:helpers helpers :kernel-policy (:kernel-policy configuration)})
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
