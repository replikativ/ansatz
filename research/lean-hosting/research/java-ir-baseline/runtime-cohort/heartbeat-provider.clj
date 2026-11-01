(ns allocation-heartbeat-lab-v1
  "Explicit get/set BaseIO lab provider. One context per engine branch, shared
   by synchronous callbacks. No Java/default-native or cumulative counter change."
  (:require [java-ir-baseline :as j]
            [ansatz.research.ir.source-setup :as source]
            [ansatz.research.ir.authenticated-demand :as demand]
            [allocation-heartbeat-counter-v1 :as counter])
  (:import [java.util WeakHashMap] [java.lang.reflect InvocationTargetException]))
(def get-symbol "lean_io_get_num_heartbeats")
(def set-symbol "lean_io_set_heartbeats")
(def specifications
  {get-symbol {:label "IO.getNumHeartbeats" :name ["str" ["str" ["anonymous"] "IO"] "getNumHeartbeats"]
               :sha "e0f4a8124b87c424e380aa9a90db4bb8bc650581d0c3d026fb9067161456db99"
               :symbol get-symbol :parameters ["void"] :borrowed [false] :result "tobject"}
   set-symbol {:label "IO.setNumHeartbeats" :name ["str" ["str" ["anonymous"] "IO"] "setNumHeartbeats"]
               :sha "cc0f4e805fbf4747f541433bfbc3fbd0e59cc29a0cd016e93425a0440455d5e7"
               :symbol set-symbol :parameters ["tobject" "void"] :borrowed [false false] :result "tagged"}})
(deftype Provider [])
(defonce ^:private providers (WeakHashMap.))
(defonce ^:private engines (WeakHashMap.))
(defn- need [ok message] (when-not ok (throw (ex-info message {:profile :allocation-heartbeat-lab-v1}))))
(defn- field [x k] (.get (doto (.getDeclaredField (class x) k) (.setAccessible true)) x))
(defn- invoke [target name types args]
  (try (.invoke (doto (.getDeclaredMethod (class target) name (into-array Class types)) (.setAccessible true)) target (object-array args))
       (catch InvocationTargetException e (throw (.getCause e)))))
(defn- holder [provider]
  (locking providers (or (.get providers provider) (throw (ex-info "Actual issued lab Provider required" {})))))
(defn- ctx [s] @(:current-ctx (:driver s)))
(defn- live! [cell]
  (let [s @cell]
    ;; Terminal holders deliberately drop driver/engine anchors. Reject state and
    ;; thread BEFORE reading/dereferencing any such anchors.
    (need (= :ready (:status s)) "Lab provider closed, failed or completing an effect")
    (need (identical? (:thread s) (Thread/currentThread)) "Lab provider is thread confined")
    (let [d (:driver s) e (:engine d) c (ctx s)]
      (need (and (identical? e (:engine s)) (identical? (:source d) (:source s))
                 (identical? (:class c) (class e)) (identical? (:program c) (field e "program"))) "Lab driver/engine/source/Program changed")
      (doseq [k ["closed" "disposed" "untrackedFailure" "advancing"]]
        (need (false? (field e k)) "Invalid lab engine lifecycle"))
      (need (identical? (field e "taskRuntime") (j/logical-sync-task-runtime c)) "Explicit logical-synchronous task runtime required")
      (source/guard-source! (:receipt s) (:source s))
      s)))
(defn- authentic-header! [s symbol header]
  (let [{:keys [name sha parameters borrowed result]} (get specifications symbol)
        _ (need name "Unsupported lab heartbeat symbol")
        entry (source/lookup-entry (:receipt s) name)]
    (need (= sha (:sha256 entry)) "Original heartbeat row SHA differs")
    (source/authenticate-canonical-header! (:source s) (:row entry) sha header)
    (need (= [parameters borrowed result]
             [(vec (j/request-value header "paramTypes")) (vec (j/request-value header "borrowed")) (j/request-value header "resultType")]) "Heartbeat Header ABI differs")
    (need (= symbol (get-in entry [:row "ir" "extern" "ext" "entries" 0 "standard" "fn"])) "Heartbeat original extern symbol differs")
    header))
(defn bootstrap-specification!
  "Authenticate setter descriptor against a genuine CodeReceipt BEFORE the first
   setter Header is registered. Returns immutable metadata, not a source grant.
   Caller supplies this descriptor to the base prepare-host-program early specs."
  [receipt]
  (let [{:keys [name sha parameters borrowed result symbol] :as spec} (get specifications set-symbol)
        entry (source/lookup-entry receipt name) row (:row entry) declaration (get-in row ["ir" "extern"])]
    (need (= sha (:sha256 entry)) "Original setter bootstrap row SHA differs")
    (need (and (= #{"extern"} (set (keys (get row "ir")))) (= name (get row "name"))
               (= parameters (mapv #(get % "ty") (get declaration "xs")))
               (= borrowed (mapv #(get % "borrow") (get declaration "xs")))
               (= result (get declaration "type"))
               (= symbol (get-in declaration ["ext" "entries" 0 "standard" "fn"]))) "Original setter bootstrap ABI differs")
    (select-keys spec [:symbol :parameters :borrowed :result])))
(defn- program-function [c spec]
  (let [functions ^objects (field (:program c) "functions")]
    (need (<= (alength functions) 150000) "Program function inventory bound")
    (when-let [f (some #(when (= (:label spec) (field % "label")) %) functions)]
      (let [header (field f "header")]
        (need (and header (= (:name spec) (j/lean-name-data (j/request-value header "name")))) "Existing heartbeat function lacks exact canonical typed Header")
        f))))
(defn- host-abi! [host spec]
  (need (and host (= [(:symbol spec) (:parameters spec) (:borrowed spec) (:result spec)]
                     [(j/request-value host "symbol") (vec (j/request-value host "paramTypes"))
                      (vec (j/request-value host "borrowed")) (j/request-value host "resultType")])) "Heartbeat host policy ABI differs")
  host)
(defn- installed-header [s symbol]
  (let [spec (get specifications symbol) f (program-function (ctx s) spec)]
    (need f "Heartbeat function not installed")
    (host-abi! (field f "hostExtern") spec)
    (authentic-header! s symbol (field f "header"))))
(defn- raw-count [s] (Long/valueOf (.getLong (doto (.getField ^Class (:class (ctx s)) "allocations") (.setAccessible true)) (:engine s))))
(defn install!
  "Adopt an authentic already-HOST setter, or install Header+spec when its Name is
   absent. An existing unavailable setter cannot be upgraded by immutable Program
   extension: reject before effects and bootstrap its host spec earlier. Getter
   remains the already installed lab getter; initial offset0 preserves behavior."
  [parent]
  (let [d (:driver parent) c @(:current-ctx d) e (:engine d)
        seed {:driver d :engine e :source (:source d) :receipt (:code-receipt parent)
              :thread (Thread/currentThread) :status :ready :offset 0N :journal nil}
        cell (atom seed) token (Provider.)
        _ (live! cell)
        _ (need (= "idle" (j/phase c e)) "Install lab pair at idle boundary")
        _ (locking engines (need (not (.containsKey engines e)) "Provider already issued for this engine"))
        getter (installed-header seed get-symbol)
        setter-spec (get specifications set-symbol)
        descriptor (bootstrap-specification! (:receipt seed))
        existing (program-function c setter-spec) existing-header (when existing (field existing "header"))
        memo-key (demand/exact-name-key (:name setter-spec)) memo (get @(:headers-by-name d) memo-key)
        _ (when memo
            (need (and (:header memo) (= (:sha setter-spec) (:sha256 memo))) "Setter Header memo digest differs")
            (authentic-header! seed set-symbol (:header memo))
            (need (or (nil? existing-header) (identical? existing-header (:header memo))) "Setter Program/memo Header identities differ"))
        entry (source/lookup-entry (:receipt seed) (:name setter-spec))
        setter (or existing-header (:header memo) (j/declaration-header (:source seed) (:row entry) (:sha256 entry)))
        _ (authentic-header! seed set-symbol setter)
        ;; Validate BEFORE changing Program, memo, provider registries or offset.
        _ (when existing
            (need (field existing "hostExtern") "Existing unavailable setter requires source bootstrap pre-registration before its first Header")
            (host-abi! (field existing "hostExtern") setter-spec))
        registry ^java.util.Map (field (:program c) "hostRegistry")
        old-specs (.get registry set-symbol)
        _ (when old-specs
            (need (= 1 (count old-specs)) "Unexpected setter host ABI inventory")
            (host-abi! (first old-specs) setter-spec))
        next (if existing c (j/register-headers c [setter] (if old-specs [] [descriptor])))]
    (swap! cell assoc :headers {get-symbol getter set-symbol setter} :status :installing)
    (locking providers (.put providers token cell))
    (locking engines (.put engines e true))
    (try
      (when-not (identical? c next)
        (j/install-program! next e)
        (reset! (:current-ctx d) next))
      (swap! (:headers-by-name d)
        (fn [m]
          (if-let [old (get m memo-key)]
            (do (need (and (identical? setter (:header old)) (= (:sha setter-spec) (:sha256 old))) "Setter Header memo changed during installation") m)
            (assoc m memo-key {:header setter :sha256 (:sha setter-spec)}))))
      (swap! cell assoc :status :ready)
      (need (identical? setter (installed-header @cell set-symbol)) "Installed setter Header identity differs")
      token
      (catch Throwable error (swap! cell assoc :status :failed :failure error)
        (throw (ex-info "Heartbeat provider installation failed; preserve actual driver" {:provider token} error))))))
(defn serve!
  "Complete ONE actual heartbeat request. All validation precedes counter effect.
   Setter Nat is immutable Long/BigInteger: its owned RC release is a no-op in this
   JVM carrier, never an arbitrary quiet release or callback. BaseIO returns DIRECT
   Nat/Unit, not IO.ok. Post-effect completion failures retain journal and quarantine."
  [provider session]
  (let [cell (holder provider) s (live! cell) d (:driver session) e (:engine s) c (ctx s)
        _ (need (and (identical? e (:engine d)) (identical? (:source s) (:source d))
                     (identical? (:current-ctx (:driver s)) (:current-ctx d))) "Foreign heartbeat session")
        request (j/host-request c e)
        _ (need (= "host-call" (j/phase c e)) "No paused heartbeat host request")
        _ (need request "Actual current HostRequest required")
        symbol (j/request-value request "symbol") spec (get specifications symbol)
        _ (need spec "Unsupported lab request")
        call (invoke e "requireHostRequest" [(class request)] [request])
        header (field (field call "function") "header")
        _ (need (identical? header (get (:headers s) symbol)) "Wrong actual heartbeat caller Header")
        _ (authentic-header! s symbol header)
        args (vec (j/request-value request "arguments"))
        _ (need (= [(:parameters spec) (:borrowed spec) (:result spec)]
                   [(vec (j/request-value request "paramTypes")) (vec (j/request-value request "borrowed")) (j/request-value request "resultType")]) "Actual request ABI differs")
        _ (need (and (= (count (:parameters spec)) (count args)) (instance? Long (peek args)) (= 0 (peek args))) "Heartbeat argument/world shape differs")
        raw (raw-count s)
        value (if (= symbol get-symbol) (counter/result-carrier (counter/read-count raw (:offset s))) 0)
        offset (if (= symbol set-symbol) (counter/set-offset raw (first args)) (:offset s))
        _ (invoke e "preflightHostCompletion" [(class call) Object] [call value])
        journal {:request request :symbol symbol :raw raw :old-offset (:offset s) :new-offset offset
                 :reply value :status :effect-pending}]
    ;; One context for the WHOLE synchronous branch. Do not key on currentTask or
    ;; reset on promise/callback entry. Native allocation/instruction/fuel untouched.
    (swap! cell assoc :status :completing :journal journal :offset offset)
    (try
      (j/resume-host! c e request value)
      (swap! cell assoc :status :ready :journal nil)
      {:status :heartbeat-replied :symbol symbol :value (str value) :native-physical-parity false}
      (catch Throwable error
        (swap! cell assoc :status :failed :journal (assoc journal :status :effect-applied-completion-failed) :failure error)
        (throw (ex-info "Heartbeat completion failed after lab effect; do not replay" {:provider provider :symbol symbol} error))))))
(defn wrap-step
  "Explicit dispatch opt-in around the actual open-driver result bundle. Preserve
   its terminal/source checks and tick accounting for BOTH heartbeat symbols.
   Original driver remains untouched/get-only when this wrapper is absent."
  [provider runtime-driver]
  (let [original-step (:runtime-step! runtime-driver) adapter (:adapter runtime-driver)
        auth (:authority runtime-driver) ticks (:ticks runtime-driver)]
    (need (and (fn? original-step) (fn? (:check-source! auth))
               (instance? clojure.lang.IAtom (:phase adapter))
               (instance? clojure.lang.IAtom ticks)) "Actual checked driver result required")
    (live! (holder provider))
    (fn [session]
      (let [d (:driver session) c @(:current-ctx d) e (:engine d)
            request (when (= "host-call" (j/phase c e)) (j/host-request c e))
            symbol (when request (j/request-value request "symbol"))]
        (if (contains? specifications symbol)
          (do
            (need (not (contains? #{:failed :retired} @(:phase adapter))) "Terminal artifact adapter")
            ((:check-source! auth) e (:source d))
            (swap! ticks inc)
            (serve! provider session))
          (original-step session))))))
(defn attach
  "Attach the actual Provider explicitly to parent AND driver routing metadata.
   No source/engine/association authority is created by this metadata."
  [parent provider]
  (let [s (live! (holder provider)) d (:driver parent)]
    (need (and (identical? (:engine s) (:engine d)) (identical? (:source s) (:source d))
               (identical? (:current-ctx (:driver s)) (:current-ctx d))) "Cannot attach foreign branch heartbeat provider")
    (assoc parent :lab-heartbeat-provider provider :driver (assoc d :lab-heartbeat-provider provider))))
(defn handles? [symbol] (contains? specifications symbol))
(defn serve-current!
  "Route from explicit parent/session metadata, including setup/options/finalizer
   and retirement loops. Never fall back to old cumulative-only getter after set."
  [session]
  (let [direct (:lab-heartbeat-provider session) driver-token (get-in session [:driver :lab-heartbeat-provider])
        _ (need (or direct driver-token) "Explicit branch heartbeat routing required")
        _ (need (or (nil? direct) (nil? driver-token) (identical? direct driver-token)) "Parent/driver heartbeat branch mismatch")]
    (serve! (or direct driver-token) session)))
(defn fork!
  "Own the actual eager fork, then clone offset VALUE into a fresh branch atom.
   Roots/RC ownership obligations are exactly j/fork!'s existing obligations.
   Caller uses returned driver/provider when building its child parent map. No active
   imported-kernel association fork is offered. Any
   failure after actual fork preserves its actual packet in the parent journal."
  [provider roots]
  (let [parent-cell (holder provider) s (live! parent-cell) d (:driver s) c (ctx s)
        _ (need (and (false? (field (:engine s) "moduleGraphInstalled"))
                     (nil? (field (:engine s) "hostGuestRecord"))) "Fork only unassociated runtime branches, not active/imported kernel sessions")
        parent-raw (raw-count s)]
    (swap! parent-cell assoc :status :forking :journal {:status :fork-pending})
    (try
      (let [packet (j/fork! c (:engine s) roots)
            _ (swap! parent-cell assoc :journal {:status :fork-returned :packet packet})
            child (:engine packet)
            child-driver (assoc d :engine child :roots (:roots packet) :current-ctx (atom c)
                                 :headers-by-name (atom @(:headers-by-name d)) :requests (atom []))
            token (Provider.) cell (atom (assoc s :driver child-driver :engine child :offset 0N :journal nil))]
        (need (= parent-raw (raw-count s)) "Fork changed parent's cumulative allocation mark")
        (swap! cell assoc :offset (counter/fork-offset parent-raw (:offset s) (raw-count @cell)))
        (locking providers (.put providers token cell))
        (locking engines (.put engines child true))
        (let [result (assoc packet :driver (assoc child-driver :lab-heartbeat-provider token) :provider token :lab-heartbeat-provider token)]
          (swap! parent-cell assoc :status :ready :journal nil)
          result))
      (catch Throwable error
        (swap! parent-cell assoc :status :failed :failure error)
        (throw (ex-info "Lab branch fork failed; preserve actual packet journal" {:provider provider} error))))))
(defn inspect [provider]
  (let [s @(holder provider)]
    (select-keys s [:status :offset :journal])))
(defn revoke!
  "Clear only host provider anchors. Keep it live through callback-capable owner
   release AND disposal; revoke after actual disposal/take (or closed engine),
   before catalogue lease closure. Failed journals cannot be discarded here."
  [provider]
  (let [cell (holder provider) s @cell e (:engine s)]
    (need (and (= :ready (:status s)) (identical? (:thread s) (Thread/currentThread))) "Revoke requires healthy owner-thread provider")
    (source/guard-source! (:receipt s) (:source s))
    (need (or (true? (field e "disposed")) (true? (field e "closed"))) "Keep provider live through cleanup: actual engine disposal or close is required")
    (need (and (identical? e (get-in s [:driver :engine]))
               (identical? (:source s) (get-in s [:driver :source]))
               (identical? (:program (ctx s)) (field e "program"))) "Disposed provider binding changed")
    (need (= "idle" (j/phase (ctx s) e)) "Revoke only after actual healthy idle completion")
    (reset! cell {:status :revoked}) nil))
