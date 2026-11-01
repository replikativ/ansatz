(ns prototype.raw-cases-on-panic-support
  "Test-only trusted host panic capability, copied from the reviewed controller.
   This is ordinary Clojure source, never untrusted guest metadata."
  (:require [prototype.machine :as m]
            [prototype.runtime-string :as runtime-string]))

(defn- check! [ok message] (when-not ok (throw (ex-info message {}))))

;; BEGIN EXACT CAPTURED FACTORY
;; Captured HOST definitions. Deliberately not a new closed runtime namespace.
(def panic-symbol "lean_panic_fn_borrowed")
(def panic-target ["str" ["anonymous"] "panicCore"])
(def panic-signature
  {:params [{:ty "erased" :borrow false} {:ty "tobject" :borrow true} {:ty "object" :borrow false}]
   :return-type "tobject"})

(defn make-panic-controller
  "Explicit bounded HOST diagnostic profile for the exact borrowed panic ABI.
   Sink receives only String including newline and must return nil. Its effects
   and finite budget are externally shared across persistent World forks.
   :return preserves nonfatal default semantics; :terminate reports then raises
   named operation failure instead of aborting/exiting this embedding JVM.
   Native backtrace and guest FS.Stream redirection are NOT emulated."
  [{:keys [policy diagnostic-sink] :as spec}]
  (check! (= #{:policy :diagnostic-sink} (set (keys spec))) "Exact panic policy and diagnostic sink required")
  (let [allowed #{:mode :messages? :backtrace? :max-message-bytes :max-output-bytes :max-events}
        expected (if (= :terminate (:mode policy)) (conj allowed :termination) allowed)]
    (check! (and (map? policy) (= expected (set (keys policy)))
                 (contains? #{:return :terminate} (:mode policy)) (boolean? (:messages? policy))
                 (false? (:backtrace? policy)) (fn? diagnostic-sink)
                 (or (= :return (:mode policy)) (contains? #{:abort :exit} (:termination policy)))
                 (integer? (:max-message-bytes policy)) (<= 1 (:max-message-bytes policy) 65536)
                 (integer? (:max-output-bytes policy)) (<= 0 (:max-output-bytes policy) 1048576)
                 (integer? (:max-events policy)) (<= 1 (:max-events policy) 4096))
            "Unsupported/unbounded explicit panic policy"))
  (let [policy (into {} policy) ledger (atom {:events 0 :bytes 0 :poisoned? false :busy? false})
        active (ThreadLocal.)
        handler
        (fn [context world arguments]
          ;; Reject before acquiring another reservation or owner. The same
          ;; handler remains busy through decoding, sink, release and failure.
          (when (.get active) (throw (ex-info "Reentrant panic diagnostic denied" {:panic-reentrant? true})))
          ;; Claim only while holding the monitor. No user sink/callback is
          ;; called under this lock: cross-thread reentry must fail, not wait
          ;; on a sink which itself is synchronously waiting for that thread.
          (locking ledger
            (when (:busy? @ledger)
              (throw (ex-info "Concurrent/reentrant panic diagnostic denied" {:panic-reentrant? true})))
            (swap! ledger assoc :busy? true))
          (.set active true)
          (let [progress (volatile! world) phase (volatile! :entry) reserved? (volatile! false)
                  owners (volatile! {})
                  publish! (fn [w] (vreset! progress w) ((:checkpoint! context) w) w)]
              (try
                (check! (and (map? context) (fn? (:checkpoint! context))
                             (= panic-symbol (:symbol context)) (= panic-signature (:signature context))
                             (vector? arguments) (= 3 (count arguments)) (= m/erased (first arguments)))
                        "Panic requires its matching raw scope and erased type argument")
                (vreset! owners {:default {:value (nth arguments 1) :state :borrowed}
                                 :message {:value (nth arguments 2) :state :owned}})
                (publish! world)
                (vreset! phase :validate-inputs)
                (let [[_ default message] arguments
                      _ (doseq [value [default message] :when (m/ref? value)]
                          (let [rc (:rc (m/node world value))]
                            ;; rc0 is the existing native/persistent exemption;
                            ;; invalid negative/missing RC must never emit.
                            (check! (and (integer? rc) (not (neg? rc)))
                                    "Panic input has invalid reference count")))
                      text (runtime-string/string-value {:ref? m/ref? :node m/node} world message)
                      _ (check! (<= (count text) (:max-message-bytes policy)) "Panic message exceeds finite bound")
                      [_ bytes] (runtime-string/evaluate {:ref? m/ref? :node m/node} world "lean_string_utf8_byte_size" [message])
                      _ (check! (<= bytes (:max-message-bytes policy)) "Panic UTF8 message exceeds finite bound")
                      output-bytes (if (:messages? policy) (inc bytes) 0)
                      old @ledger]
                  (check! (and (not (:poisoned? old)) (< (:events old) (:max-events policy))
                               (<= output-bytes (- (:max-output-bytes policy) (:bytes old))))
                          "Panic diagnostic budget exhausted or poisoned")
                  ;; Reservation precedes ALL owner changes and external effects.
                  (swap! ledger #(-> % (update :events inc) (update :bytes + output-bytes)))
                  (vreset! reserved? true)
                  (vreset! phase :retain-default)
                  (let [retained (m/retain @progress default 1)]
                    (vreset! owners (assoc @owners :default {:value default :state :owned}))
                    (publish! retained))
                  (vreset! phase :report)
                  (when (:messages? policy)
                    (check! (nil? (diagnostic-sink (str text "\n"))) "Panic diagnostic sink must return nil"))
                  (vreset! phase :reported)
                  (when (= :terminate (:mode policy))
                    ;; Native abort/exit occurs BEFORE lean_panic_fn decrefs msg.
                    ;; Keep both host-held owners and canonical checkpoint.
                    (vreset! phase :terminate)
                    (throw (ex-info "Configured Lean panic termination"
                                    {:type :lean-panic-termination :termination (:termination policy)
                                     :native-exit-code (when (= :exit (:termination policy)) 1)
                                     :host-process-terminated? false})))
                  (vreset! phase :release-message)
                  (let [released (m/release @progress message 1)]
                    (vreset! owners (assoc @owners :message {:value message :state :consumed}))
                    (publish! released))
                  (vreset! phase :return)
                  ;; The additional borrowed-default owner becomes caller-owned.
                  [@progress default])
                (catch Throwable cause
                  (when @reserved? (swap! ledger assoc :poisoned? true))
                  (throw (ex-info "Explicit panic handler failed"
                                  (merge (ex-data cause)
                                         {:checkpoint @progress :panic-entry {:world world :arguments arguments}
                                          :panic-policy policy :panic-phase @phase :panic-owners @owners
                                          :panic-ledger (select-keys @ledger [:events :bytes :poisoned?])
                                          :panic-terminal? true}) cause)))
                (finally
                  (locking ledger (swap! ledger assoc :busy? false))
                  (.remove active)))))]
    {:binding {:signature panic-signature :handler handler :guest-helper-roots []
               :panic-policy policy :panic-profile "explicit-host-diagnostic-panic/1"}
     :summary (fn [] (assoc (select-keys @ledger [:events :bytes :poisoned?]) :policy policy))}))
