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

(def ^:dynamic ^:private *conditional-installing?* false)

(defn- installation-steps [{:keys [synth-cache caches]} session env-writer]
  (concat
   (map (fn [[key cell]]
          [key (if (= key :env)
                 #(env-writer cell (:env session))
                 #(reset! cell (get session key)))]) slots)
   [[:synth-cache #(reset! synth-cache @(:synth-cache session))]]
   (map (fn [[key _ _ restore-cache]] [key #(restore-cache (get session key))]) caches)))

(defn- install! [resolved session]
  (doseq [[_ write] (installation-steps resolved session reset!)] (write))
  session)

(defn- refuse-nested-install! []
  (when *conditional-installing?*
    (throw (ex-info "Nested session installation during conditional activation"
                    {:type ::nested-installation}))))

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
  (refuse-nested-install!)
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
  (refuse-nested-install!)
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

(defn- leaves [snapshot]
  ;; capture-caches makes a fresh simp wrapper; only its actual immutable leaves
  ;; participate in identity drift checks. The synthesis Atom is also a copy.
  (-> (select-keys snapshot (concat (map first slots) [:instance-caches :simp-index-caches]))
      (assoc :synth-cache @(:synth-cache snapshot)
             :simp-cache-env (get-in snapshot [:simp-caches :env])
             :simp-cache-entries (get-in snapshot [:simp-caches :entries]))
      (dissoc :simp-caches)))

(defn- changed-leaves [expected actual]
  (into [] (keep (fn [[key value]] (when-not (identical? value (get actual key)) key))) expected))

(defn- observed [resolved]
  (try {:session (capture* resolved)}
       (catch Throwable error {:error error})))

(defn- owned-transition? [before prepared actual]
  (every? (fn [[key value]]
            (or (identical? value (get before key))
                (identical? value (get prepared key)))) actual))

(defn- restore-conditional! [resolved before prepared]
  (let [old (leaves before) target (leaves prepared)
        errors (volatile! [])
        inspect #(let [{:keys [session error]} (observed resolved)]
                   (if error {:status :conflicted :errors (conj @errors error)}
                       (let [actual (leaves session) changed (changed-leaves old actual)]
                         {:status (if (owned-transition? old target actual) :owned :conflicted)
                          :session session :changed changed :errors @errors})))]
    (loop [steps (seq (installation-steps resolved before reset!))]
      (let [{:keys [status changed] :as state} (inspect)]
        (cond
          (= :conflicted status) state
          ;; A failed validator may have made no change at all. Do not trigger
          ;; extra callbacks when the entire captured state is already restored.
          (empty? changed) (assoc state :status :restored)
          (nil? steps) (assoc state :status :failed)
          :else
          (do
            (try ((second (first steps)))
                 (catch Throwable error (vswap! errors conj error)))
            ;; Inspect again before the next write, even after a thrown watch.
            (recur (next steps))))))))

(defn- failed-conditional [resolved before prepared stage cause]
  (let [restoration (restore-conditional! resolved before prepared)]
    (doseq [error (:errors restoration)] (suppress-restoration! cause error))
    {:status :failed :stage stage :cause cause :restoration restoration}))

(defn- env-cas! [cell expected prepared]
  (compare-and-set! cell expected prepared))

(defn- install-conditional! [resolved before prepared]
  (let [old (leaves before) target (leaves prepared)
        progress (volatile! old)
        env-returned? (volatile! false)
        env-accepted? (volatile! false)
        stage (volatile! :env-cas)
        writer (fn [cell new-env]
                 (let [accepted (env-cas! cell (:env before) new-env)]
                   (vreset! env-returned? true)
                   (vreset! env-accepted? accepted)))
        steps (installation-steps resolved prepared writer)]
    (try
      (loop [remaining (seq steps)]
        (if-let [[key write] (first remaining)]
          (do
            (vreset! stage (if (= key :env) :env-cas key))
            (write)
            (if (and (= key :env) @env-returned? (not @env-accepted?))
              ;; CAS false is a rejected stale request, never an owned install.
              {:status :rejected :stage :stale-env-cas
               :changed [:env] :observation (observed resolved)}
              (let [_ (if (= key :simp-caches)
                        (vswap! progress assoc :simp-cache-env (:simp-cache-env target)
                                :simp-cache-entries (:simp-cache-entries target))
                        (vswap! progress assoc key (get target key)))
                    {:keys [session error]} (observed resolved)]
                (when error (throw error))
                (let [changed (changed-leaves @progress (leaves session))]
                  (if (seq changed)
                    ;; A successful CAS can have a silent watch that installs a
                    ;; foreign Env/session. Never continue publishing over it.
                    {:status :failed :stage @stage
                     :cause (ex-info "Session changed during conditional installation"
                                     {:type ::installation-conflict :changed changed})
                     :restoration {:status :conflicted :session session :changed changed :errors []}}
                    (recur (next remaining)))))))
          (let [{:keys [session error]} (observed resolved)]
            (when error (throw error))
            (let [changed (changed-leaves target (leaves session))]
              (if (seq changed)
                {:status :failed :stage :final-check
                 :cause (ex-info "Prepared session changed before conditional activation completed"
                                 {:type ::installation-conflict :changed changed})
                 :restoration {:status :conflicted :session session :changed changed :errors []}}
                {:status :activated :session prepared})))))
      (catch Throwable cause
        (failed-conditional resolved before prepared @stage cause)))))

(defn activate-if-unchanged!
  "Conditionally install a complete prepared context under the cooperative
   session lock. Reject identity drift before writes; make one Env CAS, without
   retry; check actual leaves after each callback. Returns an outcome map.
   Installation exceptions retain their original :cause and report verified
   best-effort :restoration. Foreign Env/leaf changes stop publication without
   overwriting that session. Watches can throw after mutation. This does not
   isolate unlocked writers/readers or undo callback side effects. Nested session
   installation during this operation is refused. Legacy APIs remain unchanged
   outside this new conditional operation. Store resources remain borrowed."
  [expected prepared]
  (if *conditional-installing?*
    {:status :rejected :stage :nested-installation :changed []}
    (locking state/session-lock
      (let [preflight
            (try
              (let [resolved (hooks)]
                {:resolved resolved :before (validate! resolved expected)
                 :prepared (validate! resolved prepared)})
              (catch Throwable cause {:cause cause}))]
        (if-let [cause (:cause preflight)]
          {:status :rejected :stage :validation :cause cause :changed []}
          (let [{:keys [resolved before prepared]} preflight
                {:keys [session error]} (observed resolved)]
            (if error
              {:status :rejected :stage :capture :cause error :changed []}
              (let [changed (changed-leaves (leaves before) (leaves session))]
                (if (seq changed)
                  {:status :rejected :stage :stale :changed changed}
                  (binding [*conditional-installing?* true]
                    (install-conditional! resolved before prepared)))))))))))
