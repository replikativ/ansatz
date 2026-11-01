(ns prototype.cooperative-driver-draft
  "Definitions-only experiment driver. No bootstrap, guest call, thread, global
   print setting, resource close or retry occurs on namespace load."
  (:require [prototype.raw-interop :as raw]
            [clojure.data.json :as json])
  (:import [java.io Writer]))

(defn- fail [message data] (throw (ex-info message data)))
(defn- bounded [text n]
  (when (string? text) (subs text 0 (min n (count text)))))
(defn- scalar-summary [event]
  (let [world (:state event)]
    {:status (:status event) :guest-status (:status world)
     :steps (get-in world [:stats :steps])
     :local-heap-objects (count (:heap world))
     :functions (count (:functions world))
     :kernel-associations (count (:kernel-environments world))
     :host-symbol (bounded (get-in world [:host-request :symbol]) 200)
     :helper-steps (:helper-steps event)
     :finish-finalization-called false}))

(defn- authorized-session! [allowed session]
  ;; A nested raw callback does not pass the outer symbol gate. Authorize the
  ;; ENTIRE active registry before entering either operation; raw's scoped
  ;; install/link/backend capabilities preserve these binding identities.
  (when-not (map? (:bindings session))
    (fail "Active session has no binding registry" {}))
  (doseq [[symbol binding] (:bindings session)]
    (when-not (and (contains? allowed symbol) (identical? binding (get allowed symbol)))
      (fail "Active session contains an unauthorized callback binding"
            {:symbol (bounded symbol 200)}))))

(deftype ^:private CooperativeDriver [ledger options])

(defn make-driver
  "Borrow an exact prepared world/session/source. :allowed-bindings is an explicit
   symbol->IDENTICAL binding allowlist captured by trusted preparation, not a
   guest-controlled list. The WHOLE active registry must be authorized, including
   callbacks reached by nested helpers; this is checked before every operation.
   :helper-fuel is an explicit nonnegative guest budget
   for EACH outer handler (e.g. 20000000), not a wall-time or overall fuel bound.
   :source-open? [source]->true is a trusted lifetime assertion. This driver never
   opens/closes the source or retains/releases any guest owner. :observe! is an
   optional scalar-summary sink; the caller owns its output resource."
  [session world {:keys [allowed-bindings helper-fuel source source-open? observe!] :as options}]
  (when-not (and (identical? (:functions session) (:functions world))
                (contains? #{:running :paused :host-call :done} (:status world))
                (map? options)
                (every? #{:allowed-bindings :helper-fuel :source :source-open? :observe!} (keys options))
                (map? allowed-bindings)
                (every? (fn [[symbol binding]]
                          (and (string? symbol) (seq symbol) (map? binding)
                               (identical? binding (get-in session [:bindings symbol])))) allowed-bindings)
                (integer? helper-fuel) (<= 0 helper-fuel Long/MAX_VALUE)
                (some? source) (fn? source-open?) (true? (source-open? source))
                (or (nil? observe!) (fn? observe!)))
    (fail "Invalid prepared cooperative driver inputs" {}))
  (authorized-session! allowed-bindings session)
  (CooperativeDriver. (atom {:phase :ready :event {:status :initial :state world :session session}}) options))

(defn checkpoint
  "Explicit diagnostic access to the last event/state/session. May contain owned
   guest values and resource references; never print or serialize this graph.
   A failed driver is terminal. These snapshots do not authorize IO retry."
  [^CooperativeDriver driver]
  @(.-ledger driver))

(defn- summarize-state [state options]
  (merge (scalar-summary (:event state))
         {:driver-phase (:phase state)
          :failure-message (some-> (:failure state) .getMessage (bounded 1500))
          :source-open (try (true? ((:source-open? options) (:source options)))
                            (catch Throwable _ false))}))

(defn summary [^CooperativeDriver driver]
  (summarize-state (checkpoint driver) (.-options driver)))

(defn- finish-slice! [ledger options phase status operations]
  ;; Build the return value from THIS event before publishing :ready. Another
  ;; caller may advance immediately after publication; never summarize it here.
  (let [state (assoc @ledger :phase phase)
        result {:status status :operations operations :summary (summarize-state state options)}]
    (reset! ledger state)
    result))

(defn jsonl-observer
  "Borrow an explicit Writer. Writes scalar JSONL only; never closes it. Output
   failure terminates driving; the completed guest event remains checkpointed."
  [^Writer writer]
  (fn [scalar-event]
    (locking writer
      (.write writer (str (json/write-str scalar-event) "\n"))
      (.flush writer))))

(defn drive-slice!
  "Run up to :max-operations explicit advance/complete operations, observing wall
   budget ONLY BETWEEN operations. Neither limit interrupts a handler or guest
   run already started. An advance uses the current adopted session's :fuel.
   A complete consumes one token under :helper-fuel; nested helpers stay sync.

   Exact event/session adoption is stored BEFORE observation. Failed execution
   or observation makes the driver terminal, with no retry/owner cleanup. Caller
   explicitly inspects checkpoints and decides resource disposal. Successful
   :done still owns the finalizer IO result and has NOT called finish-finalization.
   Separate drivers on deliberate old-world forks may repeat IO."
  [^CooperativeDriver driver {:keys [max-operations wall-ms] :as limits}]
  (when-not (and (= #{:max-operations :wall-ms} (set (keys limits)))
                (integer? max-operations) (<= 0 max-operations Long/MAX_VALUE)
                (integer? wall-ms) (<= 0 wall-ms Long/MAX_VALUE))
    (fail "Expected explicit nonnegative operation and wall budgets" {}))
  (let [ledger (.-ledger driver) options (.-options driver)
        prior @ledger started (System/nanoTime)]
    (when-not (and (= :ready (:phase prior))
                  (compare-and-set! ledger prior (assoc prior :phase :running)))
      (fail "Cooperative driver is busy, complete or terminally failed" {}))
    (try
      (loop [event (:event prior) operations 0]
        (cond
          (= :done (:status event))
          (finish-slice! ledger options :done :done operations)
          (or (= operations max-operations)
              (>= (/ (- (System/nanoTime) started) 1e6) wall-ms))
          (finish-slice! ledger options :ready :yielded operations)
          :else
          (let [_ (when-not (true? ((:source-open? options) (:source options)))
                    (fail "Borrowed native source is closed" {}))
                session (:session event) world (:state event)
                _ (authorized-session! (:allowed-bindings options) session)
                op-started (System/nanoTime)
                next-event
                (if (= :boundary (:status event))
                  (let [symbol (get-in world [:host-request :symbol])
                        allowed (get (:allowed-bindings options) symbol)]
                    (when-not (and allowed (identical? allowed (get-in session [:bindings symbol])))
                      (fail "Unstarted callback is outside the exact binding allowlist"
                            {:symbol (bounded symbol 200) :unstarted-boundary? true}))
                    (raw/complete-host-boundary (:token event) {:helper-fuel (:helper-fuel options)}))
                  (raw/advance-to-boundary session world))
                elapsed-ms (/ (- (System/nanoTime) op-started) 1e6)]
            ;; If observation throws, this exact successful event remains in the
            ;; ledger; the handler is never re-entered to regenerate its record.
            (swap! ledger assoc :event next-event)
            ;; Keep adopted session/state for diagnostics even if a future
            ;; extension introduces a foreign registry. Never execute it.
            (authorized-session! (:allowed-bindings options) (:session next-event))
            (when-let [observe! (:observe! options)]
              (observe! (assoc (scalar-summary next-event) :elapsed-ms elapsed-ms)))
            (recur next-event (inc operations)))))
      (catch Throwable cause
        ;; Keep the prior exact event/token plus any named child checkpoint in
        ;; the Throwable. Do not pair a child world with the outer token/session.
        (let [failed (swap! ledger assoc :phase :failed :failure cause)]
          (throw (ex-info "Cooperative driver stopped; no automatic retry"
                   {:driver-summary (summarize-state failed options)
                    :driver-checkpoint failed} cause)))))))
