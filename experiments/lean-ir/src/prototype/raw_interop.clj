(ns prototype.raw-interop
  "Raw, explicitly owned guest runtime callbacks, separate from public value codecs.
   Handler [context world raw-arguments] returns [world raw-result]. Owned ABI
   arguments are TRANSFERRED: the handler consumes/releases/transfers them exactly
   once; borrowed arguments need retain before an owned helper call or escape.
   No driver auto-release, implicit retain, Nat adaptation or global kernel state.
   :invoke consumes a closure target; static helper arguments follow its guest ABI.
   Kernel associations belong in snapshot key :kernel-environments.
   :switch-backend! [world backend {:cache atom :compile-threshold n}?] is synchronous/host-scoped;
   it preserves code, control, ownership and the invocation's absolute fuel limit.
   Returned sessions retain shared compiled-code caches across backend changes."
  (:require [prototype.import-ir :as ir]
            [prototype.runtime-abi :as abi]
            [prototype.scalar :as scalar]
            [prototype.native-scalar :as native]
            [prototype.program-install :as install]
            [prototype.machine :as m]
            [prototype.mutable :as u]
            [prototype.lazy-runtime :as lazy])
  (:import [java.util WeakHashMap]))

(defn- fail [message data] (throw (ex-info message data)))
(defn- signature! [shape]
  (when-not (and (map? shape) (vector? (:params shape)) (contains? shape :return-type))
    (fail "Raw binding requires an explicit ABI signature" {:signature shape}))
  (doseq [param (:params shape)]
    (when-not (and (= #{:ty :borrow} (set (keys param))) (boolean? (:borrow param)))
      (fail "Raw binding requires explicit parameter ownership" {:parameter param}))
    (ir/type! (:ty param)))
  (ir/type! (:return-type shape)) shape)
(defn- binding! [symbol binding]
  (when-not (and (string? symbol) (seq symbol) (map? binding) (fn? (:handler binding)))
    (fail "Missing raw runtime handler" {:symbol symbol}))
  (signature! (:signature binding)) binding)
(defn- shape [ext] {:params (mapv #(select-keys % [:ty :borrow]) (:xs ext)) :return-type (:type ext)})

(defn lower
  "Lower a selected raw binding only after exact arity/type/ownership validation.
   Other rows use strict runtime-abi lowering. Catalogue alias resolution remains
   the caller's choice; a selected host binding is an explicit trusted boundary."
  [bindings row]
  (let [ext (get-in row [:ir :extern]) symbol (when ext (abi/symbol-for ext))]
    (if-let [binding (get bindings symbol)]
      (let [_ (binding! symbol binding) expected (:signature binding) actual (shape ext)
            params (mapv #(get-in % [:x :idx]) (:xs ext))
            dest (inc (reduce max 0 params))]
        (when-not (and (= expected actual) (= (:name row) (:f ext))
                       (every? #(and (integer? %) (<= 0 %)) params) (= (count params) (count (set params))))
          (fail "Raw runtime binding ABI mismatch" {:symbol symbol :expected expected :actual actual}))
        [(:f ext) (with-meta {:params params :raw-extern {:symbol symbol :signature actual}
                             :body [:host symbol (mapv #(vector :var %) params) dest [:return [:var dest]]]}
                   {:runtime-param-types (mapv :ty (:xs ext))})])
      (abi/lower row))))

(defn open-functions
  ([functions bindings] (open-functions functions bindings {}))
  ([functions bindings {:keys [backend fuel cache compile-threshold] :or {backend :jvm fuel 1000000 compile-threshold 1}}]
   (when-not (contains? #{:reference :mutable :jvm} backend) (fail "Unknown raw runtime backend" {:backend backend}))
   (when-not (and (integer? fuel) (<= 0 fuel Long/MAX_VALUE)) (fail "Invalid raw runtime budget" {:fuel fuel}))
   (when-not (and (integer? compile-threshold) (<= 1 compile-threshold Integer/MAX_VALUE))
     (fail "Invalid raw compilation threshold" {:compile-threshold compile-threshold}))
   (doseq [[symbol binding] bindings] (binding! symbol binding))
   (doseq [[name function] functions :let [ext (:raw-extern function)] :when ext]
     (when-not (= (:signature ext) (:signature (get bindings (:symbol ext))))
       (fail "Raw runtime session ABI mismatch" {:name name :symbol (:symbol ext)})))
   (let [cache (or cache (when (= :jvm backend) (lazy/code-cache)))]
     (cond-> {:functions functions :bindings bindings :backend backend :fuel fuel :compile-threshold compile-threshold
              :program (when (= :jvm backend) (lazy/open-program functions {:compile-threshold compile-threshold} cache))}
       ;; Retain the same cache capability through a temporary mutable/reference
       ;; session, so switching back need not discard already compiled blocks.
       cache (assoc :cache cache)))))

(defn- session-options [session]
  (cond-> (select-keys session [:backend :fuel :compile-threshold])
    (or (get-in session [:program :cache]) (:cache session))
    (assoc :cache (or (get-in session [:program :cache]) (:cache session)))))

(def ^:private control-keys [:body :locals :joins :frames :status :result :resume-var :host-request])
(defn- world! [session world]
  (when-not (and (map? world) (= (:functions session) (:functions world)))
    (fail "Raw callback world has different executable code" {})) world)
(defn- boundary! [session parent world]
  (world! session world)
  (when-not (= (select-keys parent control-keys) (select-keys world control-keys))
    (fail "Raw handler changed guest control state" {})) world)
(defn- raw-value! [world type value]
  (cond
    (contains? #{"object" "tobject" "tagged"} type)
    (do (cond (m/ref? value) (m/node world value)
          (or (= value m/erased) (integer? value) (native/native-scalar? value) (string? value)
              (instance? prototype.machine.Tag value) (instance? prototype.machine.Builtin value)) nil
          :else (fail "Invalid raw guest object carrier" {:type type :value value})) value)
    (contains? #{"erased" "void"} type)
    (do (when-not (= value m/erased) (fail "Expected raw erased/world token" {:type type :value value})) value)
    :else (scalar/value! type value)))
(defn- resolve-target [session target]
  (if (contains? (:functions session) target) target
    (fail "Unlinked raw guest helper" {:target target})))
(defn- run-boundary [session world fuel]
  (case (:backend session)
    :reference (m/run world fuel)
    :mutable (u/freeze (u/run! (u/thaw world) fuel))
    :jvm (u/freeze (lazy/run! (:program session) (u/thaw world) fuel))))

(declare drive)
(defn- active-session [context] @(:active-session context))
(defn- invoke-helper [context parent parent-session world target args]
  (let [session (active-session context)]
    (try
      (when (some-> (:helper-run-failed context) deref)
        (fail "Completion helper budget is poisoned by a failed backend run" {}))
      (boundary! session parent world)
      (when-not (vector? args) (fail "Raw helper arguments must be a vector" {}))
      (let [clean (apply dissoc world control-keys)
            child (if (m/ref? target)
                    ;; Raw invocation consumes this closure owner. No implicit retain.
                    (m/call (assoc clean :frames [] :status :running :locals {0 target} :joins {})
                            [:closure [:var 0]] (mapv #(vector :imm %) args) nil nil)
                    (m/start clean (resolve-target session target) args))
            _ (reset! (:checkpoint context) child)
            finished (drive (dissoc context :yield-host? :pause-on-fuel?) child)
            restored (merge (apply dissoc finished control-keys) (select-keys world control-keys))]
        (reset! (:checkpoint context) restored)
        [restored (:result finished)])
      (catch Throwable cause
        (let [boundary {:checkpoint parent :session parent-session
                        :helper-entry-checkpoint world :helper-entry-session session
                        :helper {:target target :argument-count (when (vector? args) (count args))}}]
          ;; These immutable snapshots are diagnostic alternatives, not retry
          ;; authorization. The handler may already have performed external IO.
          (throw (ex-info (or (.getMessage cause) "Raw guest helper failed")
                          (assoc (ex-data cause)
                                 :checkpoint @(:checkpoint context)
                                 :checkpoint-session (active-session context)
                                 :host-boundary-checkpoint parent :host-boundary-session parent-session
                                 :helper-entry-checkpoint world :helper-entry-session session
                                 :failed-helper (:helper boundary)
                                 :host-boundaries (into [boundary] (:host-boundaries (ex-data cause)))) cause)))))))

(defn- dispatch-host [context current]
        (let [host-session (active-session context)
              {:keys [symbol arguments]} (:host-request current)
              binding (binding! symbol (get-in (active-session context) [:bindings symbol]))
              signature (:signature binding) params (:params signature)
              _ (when-not (= (count params) (count arguments)) (fail "Raw host request arity mismatch" {:symbol symbol}))
              arguments (mapv (fn [param arg] (raw-value! current (:ty param) arg)) params arguments)
              active (atom true)
              scope! (fn [] (when-not (and @active (identical? (:owner context) (Thread/currentThread)))
                             (fail "Raw callback is outside its synchronous invocation" {:symbol symbol})))
              checkpoint! (fn [state] (scope!) (boundary! (active-session context) current state)
                            (reset! (:checkpoint context) state) state)
              invoke (fn [state target args] (scope!) (invoke-helper context current host-session state target args))
              install! (fn [state bundle options]
                         (scope!) (boundary! (active-session context) current state)
                         (let [bindings (:bindings (active-session context))
                               ;; A source unit may select only an explicit
                               ;; binding already admitted by this session. All
                               ;; other externs retain normal catalogue/trap
                               ;; semantics; an ABI mismatch never falls back.
                               lower-extern (fn [row]
                                              (when (contains? bindings (abi/symbol-for (get-in row [:ir :extern])))
                                                (lower bindings row)))
                               installed (install/install-at-host-boundary state bundle
                                                                           (assoc options :lower-extern lower-extern))
                               next-world (:world installed)
                               session (active-session context)
                               next-session (open-functions (:functions next-world) (:bindings session)
                                              (session-options session))]
                           (when-not (= (select-keys state control-keys) (select-keys next-world control-keys))
                             (fail "Compiled installation changed guest control state" {}))
                           (reset! (:active-session context) next-session)
                           (reset! (:checkpoint context) next-world)
                           [next-world (dissoc installed :world)]))
              link-trusted!
              (fn [state catalogue roots validate!]
                ;; This capability is available only to trusted host handlers;
                ;; arbitrary guest compiler output must use install-compiled!.
                (scope!) (boundary! (active-session context) current state)
                (when-not (fn? validate!) (fail "Trusted linking requires authorization validation" {}))
                (let [session (active-session context) bindings (:bindings session)
                      lower-row (fn [row]
                                  (if (contains? bindings (abi/symbol-for (get-in row [:ir :extern])))
                                    (lower bindings row)
                                    (abi/lower-deferred-catalogue catalogue row)))
                      functions (ir/load-closure catalogue roots lower-row {:existing-functions (:functions state)})
                      _ (doseq [[name function] (:functions state)]
                          (when-not (identical? function (get functions name))
                            (fail "Trusted linking replaced existing executable" {:name name})))
                      new-functions (reduce-kv (fn [result name function]
                                                 (if (contains? (:functions state) name) result
                                                   (assoc result name function))) {} functions)
                      next-world (assoc state :functions functions)
                      ;; Validate before changing either active program or the
                      ;; recovery checkpoint. Failure leaves the old session.
                      _ (validate! next-world new-functions)
                      next-session (open-functions functions bindings (session-options session))]
                  (reset! (:active-session context) next-session)
                  (reset! (:checkpoint context) next-world)
                  [next-world new-functions]))
              switch-backend!
              (fn switch-backend!
                ([state backend] (switch-backend! state backend {}))
                ([state backend options]
                 (scope!) (boundary! (active-session context) current state)
                 (when-not (and (map? options) (every? #{:cache :compile-threshold} (keys options)))
                   (fail "Backend switch accepts only :cache and :compile-threshold options" {}))
                 (when (and (contains? options :cache)
                            (not (and (instance? clojure.lang.Atom (:cache options))
                                      (map? @(:cache options)))))
                   (fail "Backend switch cache must be an atom containing a map" {}))
                 (let [session (active-session context)
                       next-session (open-functions (:functions state) (:bindings session)
                                      (merge (session-options session) options {:backend backend}))]
                   ;; Session construction neither executes guest instructions nor
                   ;; changes this invocation's absolute step limit or fuel.
                   (reset! (:active-session context) next-session)
                   (reset! (:checkpoint context) state)
                   state)))
              response (try ((:handler binding) {:symbol symbol :signature signature
                                                 :invoke invoke :checkpoint! checkpoint!
                                                 :install-compiled! install!
                                                 :link-trusted! link-trusted!
                                                 :switch-backend! switch-backend!} current arguments)
                            (finally (reset! active false)))]
          (when-not (and (vector? response) (= 2 (count response)))
            (fail "Raw handler must return [world result]" {:symbol symbol}))
          (let [[state result] response]
            (boundary! (active-session context) current state)
            (reset! (:checkpoint context) state)
            ;; Ownership has already been discharged/transferred by the handler.
            (when (some-> (:helper-run-failed context) deref)
              ;; A handler may catch its helper error, but the opt-in completion
              ;; still cannot claim exact accounting or publish a success.
              (fail "Completion helper budget is poisoned by a failed backend run"
                    {:unresumed-host-result result :unresumed-host-signature signature}))
            (m/resume state (raw-value! state (:return-type signature) result)))))

(defn- drive [context world]
  (loop [world world]
    (reset! (:checkpoint context) world)
    (let [remaining (if-let [budget (:helper-fuel-left context)]
                      @budget
                      (max 0 (- (:step-limit context) (get-in world [:stats :steps]))))
          current (try
                    (run-boundary (active-session context) world remaining)
                    (catch Throwable cause
                      ;; A throwing backend need not expose its exact consumed
                      ;; steps. Only the opt-in completion budget is poisoned:
                      ;; catching a failed helper and retrying an older world
                      ;; must not recover uncharged guest execution capacity.
                      (when-let [budget (:helper-fuel-left context)]
                        (reset! budget 0)
                        (reset! (:helper-run-failed context) true))
                      (throw cause)))]
      ;; This separate aggregate counter is opt-in only. Counting run deltas
      ;; prevents repeated helpers on older immutable forks resetting the budget.
      (when-let [budget (:helper-fuel-left context)]
        (swap! budget - (- (get-in current [:stats :steps]) (get-in world [:stats :steps]))))
      (reset! (:checkpoint context) current)
      (case (:status current)
        :done current
        :host-call (if (:yield-host? context) current
                     (recur (dispatch-host context current)))
        :paused (if (:pause-on-fuel? context) current
                  (fail "Raw runtime instruction budget exhausted" {:steps (get-in current [:stats :steps])}))
        (fail "Unexpected raw runtime boundary" {:status (:status current)})))))

(defn continue
  "Drive an explicit snapshot. Failure throws with its latest immutable :checkpoint;
   this is inspection/recovery state, not permission to retry an effected handler.
   :checkpoint-session matches the latest checkpoint. Failed helpers additionally
   preserve the original :host-boundary-checkpoint/:host-boundary-session and
   their :helper-entry-checkpoint/:helper-entry-session after handler changes.
   :host-boundaries records nested callers outermost first. These alternatives
   never imply rollback of external effects or permission to retry a handler.
   Handler checkpoints and nested callbacks preserve :kernel-environments."
  [session world]
  (world! session world)
  (let [world (if (= :paused (:status world)) (m/resume world m/erased) world)
        checkpoint (atom world)
        context {:active-session (atom session) :owner (Thread/currentThread) :checkpoint checkpoint
                 :step-limit (+ (get-in world [:stats :steps]) (:fuel session))}]
    (try
      (let [finished (drive context world)]
        {:state finished :value (:result finished) :session (active-session context)})
      (catch Throwable cause
        (throw (ex-info (or (.getMessage cause) "Raw guest invocation failed")
                       (assoc (ex-data cause) :checkpoint @checkpoint :checkpoint-session (active-session context)) cause))))))

(defn call
  "Invoke a static guest entry in an explicit world. Arguments/results are raw
   ownership transfers; no public value adaptation or implicit result release."
  [session world target args]
  (world! session world)
  (when-not (vector? args) (fail "Raw call arguments must be a vector" {}))
  (continue session (m/start world (resolve-target session target) args)))


;; Deliberately process-local and non-serializable. Possession is a trusted host
;; capability, not a durable checkpoint or an untrusted deserialization format.
(deftype ^:private HostBoundaryToken [world session request binding claim])
;; Public deftype fields are not lifecycle authority. Values are scalar keywords,
;; never token/World/session/cause objects that could root their own weak keys.
(defonce ^:private boundary-phases (WeakHashMap.))
(defn- boundary-phase [token]
  (locking boundary-phases (.get ^WeakHashMap boundary-phases token)))
(defn- boundary-phase! [token phase]
  (locking boundary-phases (.put ^WeakHashMap boundary-phases token phase)))

(defn advance-to-boundary
  "Opt-in cooperative execution. Run at most session :fuel guest instructions,
   stopping BEFORE an outer host handler starts. Returns :boundary plus an opaque
   once-only token, :paused, or :done. Existing call/continue are unchanged.
   A subsequent advance has its own explicit session budget; this is not an
   implicit total-budget extension of an existing call. No handler IO is run."
  [session world]
  (world! session world)
  (let [world (if (= :paused (:status world)) (m/resume world m/erased) world)
        context {:active-session (atom session) :owner (Thread/currentThread)
                 :checkpoint (atom world) :yield-host? true :pause-on-fuel? true
                 :step-limit (+ (get-in world [:stats :steps]) (:fuel session))}]
    (try
      (let [state (drive context world) session (active-session context)]
        (case (:status state)
          :host-call
          (let [request (:host-request state)
                binding (binding! (:symbol request) (get-in session [:bindings (:symbol request)]))
                token (HostBoundaryToken. state session request binding (atom :unstarted))]
            (boundary-phase! token :unstarted)
            {:status :boundary :state state :session session :token token})
          :paused {:status :paused :state state :session session}
          :done {:status :done :state state :session session :value (:result state)}))
      (catch Throwable cause
        (throw (ex-info (or (.getMessage cause) "Raw boundary advance failed")
                 (assoc (ex-data cause) :checkpoint @(:checkpoint context)
                                       :checkpoint-session (active-session context)) cause))))))

(defn complete-host-boundary
  "Consume an advance-to-boundary token once. Execute exactly one outer handler
   using the existing dispatcher/capabilities, then m/resume once and RETURN;
   no outer guest instruction is run. :helper-fuel is mandatory and bounds the
   AGGREGATE guest instructions across synchronous helpers and nested callbacks.
   It does not bound host CPU, native IO, checker work, compilation or wall time.

   A throwing backend poisons this completion even if its handler catches the
   helper exception: no further helper call or success receipt is permitted.
   A started failure consumes the private issued phase permanently. Its child checkpoint and
   named outer boundary are diagnostics, NOT retry/resume authorization: the
   host continuation was unwound and external effects cannot be rolled back.
   Tokens do not prevent IO replay by a caller deliberately forking old worlds."
  [token {:keys [helper-fuel] :as options}]
  (when-not (and (instance? HostBoundaryToken token)
                (map? options) (= #{:helper-fuel} (set (keys options)))
                (integer? helper-fuel) (<= 0 helper-fuel Long/MAX_VALUE))
    (fail "Expected a boundary token and explicit nonnegative helper-fuel" {}))
  (locking token
    (when-not (boundary-phase token) (fail "Expected an issued raw host boundary token" {})))
  (let [world (.-world ^HostBoundaryToken token)
        session (.-session ^HostBoundaryToken token)
        request (.-request ^HostBoundaryToken token)
        binding (.-binding ^HostBoundaryToken token)]
    (world! session world)
    (when-not (and (= :host-call (:status world))
                  (identical? request (:host-request world))
                  (identical? binding (get-in session [:bindings (:symbol request)])))
      (fail "Boundary token does not match its captured request/session" {}))
    ;; Allocate the complete context before the private claim. Allocation
    ;; failure here leaves it unstarted; after claim dispatch is inside try.
    ;; No public claim Atom is read/written: hooks/reset cannot grant authority.
    (let [context {:active-session (atom session) :owner (Thread/currentThread)
                   :checkpoint (atom world) :step-limit Long/MAX_VALUE
                   :helper-fuel-left (atom helper-fuel) :helper-run-failed (atom false)}]
      (locking token
        (when-not (= :unstarted (boundary-phase token))
          (fail "Boundary token has already been consumed" {}))
        (boundary-phase! token :started))
      (try
        (let [state (dispatch-host context world)]
          (locking token (boundary-phase! token :completed))
          {:status :handler-completed :state state :session (active-session context)
           :helper-steps (- helper-fuel @(:helper-fuel-left context))})
        (catch Throwable cause
          (locking token (boundary-phase! token :failed))
          (throw (ex-info (or (.getMessage cause) "Raw boundary handler failed")
                   (assoc (ex-data cause)
                          :checkpoint @(:checkpoint context)
                          :checkpoint-session (active-session context)
                          :boundary-completion :failed :boundary-token-consumed? true
                          :unstarted-outer-checkpoint world :unstarted-outer-session session)
                   cause)))))))


(defn abandon-host-boundary!
  "Retire an issued boundary without touching its public claim Atom or handler.
   Private scalar phases and token lock exclude completion/disposal races. No
   rollback, native finalization, or revocation of copied old Worlds is implied."
  [token]
  (when-not (instance? HostBoundaryToken token)
    (fail "Expected an issued raw host boundary token" {}))
  (locking token
    (case (boundary-phase token)
      :unstarted (do (boundary-phase! token :abandoned-unstarted)
                     {:phase :abandoned :completion-already-attempted false})
      (:completed :failed) (do (boundary-phase! token :abandoned-attempted)
                               {:phase :abandoned :completion-already-attempted true})
      :abandoned-unstarted {:phase :abandoned :completion-already-attempted false}
      :abandoned-attempted {:phase :abandoned :completion-already-attempted true}
      :started (fail "Cannot abandon a running host boundary" {})
      (fail "Expected an issued raw host boundary token" {}))))
