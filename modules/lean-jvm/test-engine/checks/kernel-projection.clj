(ns ansatz.research.ir.kernel-projection
  "Invocation-local borrowed Java Node storage views for existing kernel rules.
   No guest ownership/state changes and no whole-graph clone. Exact class/kind
   validation is not source membership: caller must supply the actual borrowed
   HostRequest argument (or an explicitly owned helper result). Close BEFORE
   any guest/helper/release/resume operation, even if a stamp happens to match."
  (:require [kernel-support.kernel-bridge :as bridge]
            [kernel-support.constructor-layout :as constructor])
  (:import [java.util IdentityHashMap] [java.lang.reflect InvocationTargetException]))
(defn- nano-time [] (System/nanoTime))
(defn- fail [message data] (throw (ex-info message data)))
(defn- private-field [^Class cls name]
  (doto (.getDeclaredField cls name) (.setAccessible true)))
(defn- invoke0 [target name]
  (.invoke (.getMethod (class target) name (make-array Class 0)) target (object-array 0)))
(defn- guest-stamp [state phase]
  (let [engine (:engine state)
        record (.get ^java.lang.reflect.Field (:host-guest-record state) engine)
        completion (.get ^java.lang.reflect.Field (:host-completion state) engine)
        read (fn [key] (when record (.get ^java.lang.reflect.Field (get-in state [:guest-fields key]) record)))
        token (read :token) outer (read :outer) result (read :result)
        flags (when record (mapv read [:complete :result-owned :taken :arguments-owned]))]
    (when (= "host-guest-result" phase)
      ;; This is a completed helper, with its outer request still parked. The
      ;; result remains owned by the actual record until the one-shot take.
      ;; A claimed HostCompletion prefix is legal and must remain unchanged.
      (when-not (and record token outer (some? result)
                     (= [true true false false] flags)
                     (identical? token (invoke0 engine "pendingHostGuestResult"))
                     (identical? record (.get ^java.lang.reflect.Field (:token-record state) token))
                     (identical? (.get ^java.lang.reflect.Field (:runtime-identity state) engine)
                                 (.get ^java.lang.reflect.Field (:token-owner state) token))
                     (identical? completion (read :completion-base))
                     (nil? (.get ^java.lang.reflect.Field (:host-request state) engine))
                     (nil? (.get ^java.lang.reflect.Field (:code-request state) engine)))
        (fail "HostGuest result is not a quiescent owned lending boundary" {})))
    {:host-guest-record record :host-guest-token token :host-guest-outer outer
     :host-guest-parent (read :parent) :host-guest-result result
     :host-completion completion :completion-base (read :completion-base) :guest-flags flags}))
(defn- stamp [state]
  (let [engine (:engine state)]
    (doseq [key [:closed :untracked-failure :disposed]]
      (when (.getBoolean ^java.lang.reflect.Field (get state key) engine)
        (fail "Engine cannot lend kernel values after close/failure/disposal" {:lifecycle key})))
    (when (.getBoolean ^java.lang.reflect.Field (:advancing state) engine)
      (fail "Kernel projection requires a paused engine" {}))
    (let [phase (invoke0 engine "phase")]
      (when-not (contains? #{"idle" "host-call" "code-call" "complete" "running" "host-guest-result"} phase)
        (fail "Engine phase cannot lend kernel values" {:phase phase}))
      (merge (guest-stamp state phase)
       {:phase phase :instructions (invoke0 engine "instructionCount")
       :program (.get ^java.lang.reflect.Field (:program state) engine)
       :pc (.get ^java.lang.reflect.Field (:pc state) engine)
       :request (.get ^java.lang.reflect.Field (:host-request state) engine)
       :code-request (.get ^java.lang.reflect.Field (:code-request state) engine)
       :runtime-action (.get ^java.lang.reflect.Field (:runtime-action state) engine)
       :counters (mapv #(.getLong ^java.lang.reflect.Field % engine) (:counters state))}))))
(defn- live! [holder]
  (let [state @holder]
    (when-not state (fail "Kernel projection scope is closed" {}))
    (when-not (identical? (:thread state) (Thread/currentThread))
      (fail "Kernel projection scope belongs to another thread" {}))
    (when (> (nano-time) (:deadline-nanos state))
      (fail "Kernel projection deadline exceeded" {}))
    (let [now (stamp state) before (:stamp state)]
      (when-not (and (= (select-keys now [:phase :instructions :counters :guest-flags])
                       (select-keys before [:phase :instructions :counters :guest-flags]))
                     (every? #(identical? (get now %) (get before %))
                             [:program :pc :request :code-request :runtime-action
                              :host-guest-record :host-guest-token :host-guest-outer :host-guest-parent
                              :host-guest-result :host-completion :completion-base]))
        (fail "Engine progressed during borrowed kernel projection" {})))
    state))
(defn- view! [holder ^IdentityHashMap memo token world value]
  (when-not (identical? token world) (fail "Java carrier belongs to a different projection scope" {}))
  (let [state (live! holder) node-class ^Class (:node-class state)]
    (when-not (and (some? value) (identical? node-class (class value)))
      (fail "Expected exact Java interpreter Node class" {}))
    ;; Use the current engine's readonly common-kind/owner/dead guard, then
    ;; explicitly exclude closures (which also use ordinary allocation storage).
    (try (.invoke ^java.lang.reflect.Method (:ctor-guard state) (:engine state) (object-array [value]))
         (catch InvocationTargetException error (throw (.getCause error))))
    (when (.get ^java.lang.reflect.Field (:closure state) value)
      (fail "Closure is not a kernel constructor" {}))
    (or (.get memo value)
        (do
          (when (>= (.size memo) (:max-nodes state))
            (fail "Kernel projection source-node limit exceeded" {:limit (:max-nodes state)}))
          (let [fields ^objects (.get ^java.lang.reflect.Field (:fields state) value)
                bytes ^bytes (.get ^java.lang.reflect.Field (:scalars state) value)
                n (alength fields) extent (alength bytes)
                tag (.getInt ^java.lang.reflect.Field (:tag state) value)]
            (when-not (and (<= 0 tag 243) (< n 256) (< extent 1024))
              (fail "Java kernel constructor storage outside pinned profile" {:tag tag :fields n :scalar-bytes extent}))
            (let [node {:kind :ctor :tag tag :fields (vec fields)
                        :layout (when (pos? extent) {:objects n :usize 0 :ssize extent})
                        :scalar-bytes (into {} (map (fn [i] [(+ (* 8 n) i) (Byte/toUnsignedInt (aget bytes i))]) (range extent)))}
                  ;; Existing complete raw-clone storage proof admits native
                  ;; alignment padding. No native source/identity is fabricated.
                  node (if (zero? (rem extent 8)) (constructor/clone-storage node) node)]
              (.put memo value node) node))))))
(defn open-projector
  "Borrow values during ONE paused synchronous checking operation.
   Limits are {:max-nodes positive-int :deadline-nanos absolute-nanoTime}.
   Return {:world opaque-token :projector fn :carrier-ops ops :close! fn}.
   Alternate imported-CI memos created from carrier-ops must be cleared by their
   owner before close; no derived scope may survive this scope. Always close in finally.
   Close invalidates first, clears semantic/view memos and clears the only engine
   holder. Retaining a closed scope/projector does not retain guest Nodes/engine.
   Returned kernel values remain ordinary caller values. Name/Expr/Level DAGs
   are immutable; ConstantInfo freezing/snapshot/admission is a separate policy."
  [basis engine {:keys [max-nodes deadline-nanos] :as limits}]
  (when-not (and (= #{:max-nodes :deadline-nanos} (set (keys limits)))
                 (integer? max-nodes) (<= 1 max-nodes 100000)
                 (integer? deadline-nanos) (<= Long/MIN_VALUE deadline-nanos Long/MAX_VALUE)
                 (> deadline-nanos (nano-time)))
    (fail "Java kernel projection requires explicit bounded node/deadline limits" {}))
  (when-not (identical? (:class basis) (class engine))
    (fail "Interpreter basis/class differs from borrowed engine" {}))
  (let [cls ^Class (:class basis) node-class ^Class (:node-class basis)
        guest-class (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter$HostGuestRecord" false (:loader basis))
        token-class (Class/forName "ansatz.lean.jvm.internal.exec.Interpreter$HostGuestOperation" false (:loader basis))
        guard (doto (.getDeclaredMethod cls "constructorNode" (into-array Class [Object])) (.setAccessible true))
        state {:engine engine :thread (Thread/currentThread) :node-class node-class
               :max-nodes max-nodes :deadline-nanos deadline-nanos
               :closed (private-field cls "closed") :untracked-failure (private-field cls "untrackedFailure")
               :disposed (private-field cls "disposed")
               :advancing (private-field cls "advancing") :program (private-field cls "program")
               :pc (private-field cls "pc") :host-request (private-field cls "hostRequest")
               :code-request (private-field cls "codeRequest") :runtime-action (private-field cls "runtimeAction")
               :host-guest-record (private-field cls "hostGuestRecord") :host-completion (private-field cls "hostCompletion")
               :runtime-identity (private-field cls "runtimeIdentity")
               :token-record (private-field token-class "record") :token-owner (private-field token-class "owner")
               :guest-fields (into {} (map (fn [[k name]] [k (private-field guest-class name)])
                                   [[:token "token"] [:outer "outer"] [:parent "parent"] [:result "result"]
                                    [:completion-base "completionBase"] [:complete "complete"] [:result-owned "resultOwned"]
                                    [:taken "taken"] [:arguments-owned "argumentsOwned"]]))
               :counters (mapv #(private-field cls %) ["allocations" "stores" "retains" "releases" "shellDeletes"])
               :ctor-guard guard :closure (private-field node-class "closure")
               :fields (:fields basis) :scalars (:scalars basis) :tag (:tag basis)}
        holder (atom (assoc state :stamp (stamp state)))
        token (Object.) views (IdentityHashMap.)
        ops {:ref? (fn [value] (and (some? value) (identical? node-class (class value))))
             :node (fn [world value] (view! holder views token world value))
             :check! (fn [] (live! holder) nil)}
        projector (bridge/make-projector token ops)
        close! (fn []
                 ;; Locking the semantic memo first follows the same order as
                 ;; traversal; this scope is thread-confined, not a concurrent API.
                 (reset! holder nil)
                 ((:kernel-support.kernel-bridge/clear-memo! (meta projector)))
                 (.clear views)
                 nil)]
    {:world token :projector projector :carrier-ops ops :close! close!
     :stats (fn [] {:open? (some? @holder) :borrowed-views (.size views)
                    :projected-values ((:kernel-support.kernel-bridge/memo-size (meta projector)))})}))
