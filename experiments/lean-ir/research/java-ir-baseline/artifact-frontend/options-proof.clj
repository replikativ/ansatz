(ns heartbeat-lab-options-proof
  "Definition-only lab option proof. Genuine guest setters/getters; no native
   heartbeat substitution. Requires the retained sequential probe definitions."
  (:require [java-ir-baseline :as j] [sequential-frontend-probe :as sp])
  (:import [java.lang.reflect InvocationTargetException]))
(def lean-pin "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
(def row-pins
  {"Lean.Elab.Command.mkState" "402833407b9baaeb812b03555a1f72d2ddc464d19297e0c463e1fd54548aab30"
   "Lean.Options.set" "ea6242c9665e883a6aa5ee44be8e5a961ab1ebb60ae2fe2c5113f3aa3480e34a"
   "Lean.KVMap.instValueNat" "6add10b15ee0897bf74885010503365ec117b93fd3ae1df7bd02346dba16ffa3"
   "Lean.Options.get._boxed" "4c373c0226d2e148924ac92f34a58fc1de621ba465aea373b24e96f76a8f8330"
   "Lean.Options.getBool._boxed" "313926d62d58a7de6dd8a371746222a7a020a795cffa1670ed650aa1719611bd"
   "Lean.Core.getMaxHeartbeats._boxed" "3394cfcf528e9fc3ee71909101c6cb9bbd443eaa0b693ebda4919cc599f3ab46"})
(defn- need [condition message] (when-not condition (throw (ex-info message {:profile :lab-disabled-native-limits}))))
(defn- private-field [object name]
  (.get (doto (.getDeclaredField (class object) name) (.setAccessible true)) object))
(defn- guard [s method value]
  (let [m (doto (.getDeclaredMethod (class (sp/engine s)) method (into-array Class [Object])) (.setAccessible true))]
    (try (.invoke m (sp/engine s) (object-array [value]))
         (catch InvocationTargetException error (throw (.getCause error))))))
(defn- idle! [s]
  (need (= "idle" (j/phase (sp/ctx s) (sp/engine s))) "Option proof requires idle engine")
  (need (nil? @(:in-flight s)) "Option proof requires no unclaimed operation")
  (doseq [key ["closed" "disposed" "untrackedFailure" "advancing"]]
    (need (false? (private-field (sp/engine s) key)) "Invalid engine lifecycle for option proof"))
  (need (identical? (:program (sp/ctx s)) (private-field (sp/engine s) "program")) "Driver Program differs from engine") s)
(defn rebase-idle-deadline
  "Explicit lab allowance for host idle time: return session with a fresh <=60s
   cooperative deadline. Preserves ALL used-counter atoms, owner entries, calls,
   observations, limits, engine and continuation. Does not resume a boundary."
  ([s] (rebase-idle-deadline s 60000))
  ([s milliseconds]
   (idle! s)
   (need (and (integer? milliseconds) (<= 1 milliseconds 60000)) "Deadline allowance must be 1..60000ms")
   (assoc s :deadline-nanos (+ (System/nanoTime) (* 1000000 milliseconds)))))
(defn- header! [s label]
  (let [h ((sp/host-helper "ensure-header!") (:driver s) (sp/typed-name label))]
    (need (and (get row-pins label)
               (= (get row-pins label) (j/request-value h "originalSha256"))
               (identical? (get-in s [:driver :source]) (j/request-value h "source")))
          "Option proof requires exact original source/Header pin") h))
(defn- call! [s label arguments]
  (header! s label) (sp/call! s label arguments))
(defn set-owned-options-zero!
  "Before mkState only: consume/replace the actual owned options entry at key.
   Uses original Options.set with actual Nat instance. On a genuine boundary,
   preserve s/:in-flight and do not reconstruct an already transferred credit."
  [s key]
  (idle! s)
  (doseq [option ["maxHeartbeats" "maxRecDepth"]]
    (let [name (sp/call! s "Lean.Name.mkStr1" [option])
          instance (call! s "Lean.KVMap.instValueNat" [])]
      (sp/hold! s key (call! s "Lean.Options.set" [0 instance (sp/take-owner! s key) name 0]))))
  {:status :actual-options-set :session s :owner-key key})
(defn- ctor! [s value tag fields scalar-bytes]
  (guard s "constructorNode" value)
  (need (nil? (private-field value "closure")) "Expected ordinary constructor, not closure")
  (let [fs (sp/ctor! s value tag fields)]
    (need (= scalar-bytes (alength ^bytes (sp/scalars s value))) "Compiled semantic scalar layout differs") fs))
(defn- current-view! [s]
  (idle! s)
  ;; Own :state-ref anchors this borrowed traversal. No retain, set, or DEC here.
  (let [reference (guard s "reference" (sp/owned s :state-ref))
        rf (sp/fields s reference)
        _ (need (= 1 (alength ^objects rf)) "Unexpected Ref slot layout")
        state (aget ^objects rf 0)
        command (aget ^objects (ctor! s state 0 4 0) 0)
        cf (ctor! s command 0 11 0)
        scopes (aget ^objects cf 2)
        scope (aget ^objects (ctor! s scopes 1 2 0) 0)
        sf (ctor! s scope 0 10 3)]
    ;; Original mkState row: State var20 fields[2]=List.cons var10,
    ;; fields[5]=var14 actual maxRecDepth getter; Scope var9 fields[1]=opts var3.
    (let [options (aget ^objects sf 1)
          _ (ctor! s options 0 1 1)
          has-trace (Byte/toUnsignedInt (aget ^bytes (sp/scalars s options) 0))]
      (need (contains? #{0 1} has-trace) "Options.hasTrace is not a Bool byte")
      ;; Options.map is NameMap/DTreeMap, NOT the legacy list-backed KVMap.
      {:command command :scope scope :options options :cached-max-rec-depth (aget ^objects cf 5)})))
(defn- options-owner! [s view]
  ;; Boxed facades consume one credit; original unboxed helper borrows internally.
  (j/retain! (sp/ctx s) (sp/engine s) (:options view)) (:options view))
(defn- nat-option! [s view name]
  (let [key (sp/call! s "Lean.Name.mkStr1" [name])
        instance (call! s "Lean.KVMap.instValueNat" [])]
    ;; Genuine generic Options.get dispatches the Nat Value instance against
    ;; Options.map/NameMap. The owned boxed wrapper releases its borrowed args.
    ;; Nonzero fallback proves explicit 0, rather than a missing/default-zero key.
    (call! s "Lean.Options.get._boxed" [0 instance (options-owner! s view) key 1])))
(defn- bool-option! [s view prefix leaf]
  (let [key (sp/call! s "Lean.Name.mkStr2" [prefix leaf])]
    (call! s "Lean.Options.getBool._boxed" [(options-owner! s view) key 1])))
(defn check-prepared!
  "After successful setup!, before step!: prove actual current scope options and
   cached Command.State depth. Requires idle and a still-live session owner map.
   Returns scalar-only receipt plus the same session. Original guest calls share
   session dispatch/code/deadline limits. No option/state mutation is performed.
   Genuine failures preserve original exception and precise sp/:in-flight packet."
  [s]
  (header! s "Lean.Elab.Command.mkState")
  (let [view (current-view! s)
        _ (need (= 0 (:cached-max-rec-depth view)) "Command.State cached maxRecDepth is not zero")
        heartbeat-option (nat-option! s view "maxHeartbeats")
        depth-option (nat-option! s view "maxRecDepth")
        async-option (bool-option! s view "Elab" "async")
        skip-kernel-option (bool-option! s view "debug" "skipKernelTC")
        effective-heartbeats (call! s "Lean.Core.getMaxHeartbeats._boxed" [(options-owner! s view)])
        extra-bools (into {} (for [[prefix leaf] (get (sp/ctx s) :lab-false-bool-options [])]
                              [(str prefix "." leaf) (bool-option! s view prefix leaf)]))
        _ (need (every? zero? (vals extra-bools)) "Additional explicit lab Bool options are not false")
        after (current-view! s)]
    (need (and (identical? (:command view) (:command after))
               (identical? (:scope view) (:scope after))
               (identical? (:options view) (:options after))) "Option proof changed command scope identity")
    (when-not (= [0 0 0 0 0] [heartbeat-option depth-option async-option skip-kernel-option effective-heartbeats])
      (throw (ex-info "Actual frontend options/effective heartbeat limit differ from checked lab profile"
                      {:profile :lab-disabled-native-limits :max-heartbeats heartbeat-option
                       :max-rec-depth depth-option :async async-option :skip-kernel-tc skip-kernel-option
                       :effective-max-heartbeats effective-heartbeats
                       :cached-max-rec-depth (:cached-max-rec-depth after)})))
    {:status :lab-options-proved :session s :lean-commit lean-pin :row-pins row-pins
     :scope-max-heartbeats heartbeat-option :scope-max-rec-depth depth-option
     :cached-command-max-rec-depth (:cached-max-rec-depth after)
     :core-effective-max-heartbeats effective-heartbeats :elab-async async-option
     :skip-kernel-tc skip-kernel-option :kernel-checking-enabled true
     :additional-explicit-lab-bools extra-bools
     :counter-scope :lab-engine-allocations-not-native-heartbeat-parity
     :budget @(:used s) :checked-declaration-established false}))
;; Definition-only retained REPL use (NO JVM launch):
;; (load-file ABSOLUTE-options-proof-path)
;; (def proved (heartbeat-lab-options-proof/check-prepared!
;;               (heartbeat-lab-options-proof/rebase-idle-deadline (:session kernel-setup))))
;; Inspect :lab-options-proved BEFORE first step. Use (:session proved) thereafter.
;; rebase-idle-deadline is an explicit lab host-idle allowance; it never resets
;; used instruction/code/turn/command counters or silently bypasses a boundary.
;; IO.getNumHeartbeats host binding is separately reviewed/configured by root;
;; this helper neither registers it nor claims native counter/cancellation parity.
