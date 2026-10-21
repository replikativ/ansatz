(ns ansatz.session
  "Scoped installation of proof-session state over the existing ProofContext.
   Session operations serialize on state/session-lock; ordinary unlocked DSL
   mutations do not. Store handles are borrowed. This does not roll back IO,
   namespace Vars, registries or catalogue connections."
  (:require [ansatz.state :as state]
            [ansatz.recall :as recall]
            [ansatz.tactic.instance :as instance]
            [ansatz.simp-index :as simp-index]
            [ansatz.tactic.simp :as simp])
  (:import [ansatz.kernel Env]
           [clojure.lang Atom]))

(defn- hooks
  "Resolve every lazy dependency before any session state changes."
  []
  (let [constructor @(requiring-resolve 'ansatz.core/map->ProofContext)
        synth-cache @(requiring-resolve 'ansatz.core/synth-cache)]
    (when-not (instance? Atom synth-cache)
      (throw (ex-info "Missing global synthesis cache" {})))
    {:constructor constructor
     :context-class (class (constructor {}))
     :synth-cache synth-cache
     :caches [[:instance-caches instance/capture-caches instance/validate-caches! instance/restore-caches!]
              [:simp-index-caches simp-index/capture-caches simp-index/validate-caches! simp-index/restore-caches!]
              [:simp-caches simp/capture-caches simp/validate-caches! simp/restore-caches!]]}))

(def ^:private slots
  [[:env state/ansatz-env]
   [:instance-index state/ansatz-instance-index]
   [:discr-trie state/ansatz-discr-trie]
   [:simp-trie state/ansatz-simp-trie]
   [:store state/ansatz-store]
   [:recall-store-path recall/store-path]])

(defn- capture* [{:keys [constructor synth-cache caches]}]
  (constructor
   (reduce (fn [snapshot [key capture-cache]] (assoc snapshot key (capture-cache)))
           (assoc (into {} (map (fn [[key cell]] [key @cell]) slots))
                  :synth-cache (atom @synth-cache))
           caches)))

(defn- validate! [{:keys [context-class caches]} session]
  (when-not (and (.isInstance ^Class context-class session)
                 (every? #(contains? session (first %)) slots)
                 (or (nil? (:env session)) (instance? Env (:env session)))
                 (every? #(or (nil? (get session %)) (map? (get session %)))
                         [:instance-index :discr-trie :simp-trie :store])
                 (instance? Atom (:synth-cache session)))
    (throw (ex-info "Invalid proof session snapshot" {})))
  (let [synthesis @(:synth-cache session)]
    (when-not (map? synthesis)
      (throw (ex-info "Invalid synthesis cache snapshot" {})))
    (doseq [[key _ validate-cache] caches]
      (when-not (contains? session key)
        (throw (ex-info "Missing proof session cache" {:cache key})))
      (validate-cache (get session key)))
    ;; Do not read a caller-mutable cache atom again after preflight.
    (assoc session :synth-cache (atom synthesis))))

(defn- install! [{:keys [synth-cache caches]} session]
  (doseq [[key cell] slots] (reset! cell (get session key)))
  (reset! synth-cache @(:synth-cache session))
  (doseq [[key _ _ restore-cache] caches] (restore-cache (get session key)))
  session)

(defn capture
  "Capture all session globals and tactic caches as a ProofContext. Its synthesis
   cache atom is independent of the live atom. nil Env captures pre-init state."
  []
  (locking state/session-lock
    (capture* (hooks))))

(defn- suppress-restoration! [^Throwable error ^Throwable restoration]
  ;; A persistent failing hook/watch may throw one preallocated Throwable on
  ;; both attempts. Java forbids self-suppression and would mask that failure.
  (when-not (identical? error restoration)
    (.addSuppressed error restoration)))

(defn activate!
  "Install a complete captured/prepared session after validation. Restore prior
   state on installation failure. Borrow store resources without opening/closing."
  [session]
  (locking state/session-lock
    (let [resolved (hooks)
          session (validate! resolved session)
          previous (capture* resolved)]
      (try
        (install! resolved session)
        (catch Throwable error
          (try (install! resolved previous)
               (catch Throwable restoration (suppress-restoration! error restoration)))
          (throw error))))))

(defn with-session
  "Call zero-argument f with session installed, returning {:value v :session updated}.
   Hold the reentrant session lock for the entire body; restore previous session
   in finally, including nested calls and exceptions. External effects persist."
  [session f]
  (when-not (ifn? f) (throw (ex-info "Session body must be callable" {})))
  (locking state/session-lock
    (let [resolved (hooks)
          session (validate! resolved session)
          previous (capture* resolved)
          failure (volatile! nil)]
      (try
        (install! resolved session)
        (let [value (f)] {:value value :session (capture* resolved)})
        (catch Throwable error
          (vreset! failure error)
          (throw error))
        (finally
          (try (install! resolved previous)
               (catch Throwable restoration
                 (if-let [error @failure]
                   (suppress-restoration! error restoration)
                   (throw restoration)))))))))
