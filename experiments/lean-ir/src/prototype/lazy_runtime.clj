(ns prototype.lazy-runtime
  "Demand-compiled regions with a shared in-memory code cache and immutable worlds.
  :compile-threshold (default1) counts visits per body identity in this program;
  cold bodies execute one exact interpreter step. Hotness is host optimization
  state, never part of a guest snapshot, and identical-body cached code is usable immediately. Structurally equivalent
  independently parsed bodies consult the shared content cache on promotion."
  (:refer-clojure :exclude [run!])
  (:require [prototype.block-compile :as b]
            [prototype.machine :as m]
            [prototype.fingerprint :as fingerprint]
            [prototype.mutable :as u])
  (:import [java.util IdentityHashMap HashMap ArrayList]
           [java.lang.ref WeakReference ReferenceQueue]))

(defn code-cache [] (atom {}))

(defn open-program
  ([functions] (open-program functions {} (code-cache)))
  ([functions options] (open-program functions options (code-cache)))
  ([functions options cache]
   (let [options (b/prepare-program-options functions (merge {:compile-threshold 1
                         :lexical-joins true
                         :direct-linking (boolean (:direct-linking *compiler-options*))} options))]
     (when-not (and (integer? (:compile-threshold options))
                    (<= 1 (:compile-threshold options) Integer/MAX_VALUE))
       (m/fail "Invalid lazy compilation threshold" {:compile-threshold (:compile-threshold options)}))
     (b/runtime-block-key-prepared functions [:return [:imm 0]] options)
     {:functions functions :options options :cache cache
      :visits (IdentityHashMap.) :identity-keys (IdentityHashMap.)
      :generation (b/compiler-token) :dispatch (atom {}) :identity-dispatch (IdentityHashMap.)
      :counts (atom {:compiled 0 :cache-hits 0})})))

(defn summary [program]
  (assoc @(:counts program) :dispatch-blocks (count @(:dispatch program))
         :cached-blocks (count @(:cache program))))

(defn- check! [program machine]
  (when-not (identical? (:generation program) (b/compiler-token))
    (m/fail "Reopen lazy program after compiler reload" {}))
  (when-not (= (:functions program) (:functions machine))
    (m/fail "Compiled program does not match machine code" {})))

(def ^:private hint-limit 65536)

(defn- hint-table []
  {:buckets (HashMap.) :queue (ReferenceQueue.) :size (volatile! 0)})

(defonce ^:private shared-hints (hint-table))

(defn- clean-hints! []
  ;; Call under the table lock. Bucket keys are scalar identity hashes; neither
  ;; vector hashCode nor structural equality is used anywhere in this index.
  (let [^HashMap buckets (:buckets shared-hints)
        ^ReferenceQueue queue (:queue shared-hints)]
    (loop []
      (when-let [dead (.poll queue)]
        (let [key (.hashCode dead) ^ArrayList bucket (.get buckets key)]
          (when bucket
            (loop [i (dec (.size bucket))]
              (when (<= 0 i)
                (when (identical? dead (first (.get bucket i)))
                  (.remove bucket (int i))
                  (vswap! (:size shared-hints) dec))
                (recur (dec i))))
            (when (.isEmpty bucket) (.remove buckets key))))
        (recur)))))

(defn- hint-keys [body]
  (locking shared-hints
    (clean-hints!)
    (let [^ArrayList bucket (.get ^HashMap (:buckets shared-hints) (System/identityHashCode body))]
      (some (fn [[^WeakReference reference keys]]
              (when (identical? body (.get reference))
                (into [] (keep #(.get ^WeakReference %)) keys))) bucket))))

(defn- remember-hint! [body canonical-key]
  (locking shared-hints
    (clean-hints!)
    (let [^HashMap buckets (:buckets shared-hints)
          key (System/identityHashCode body)
          ^ArrayList bucket (or (.get buckets key) (ArrayList.))
          entry (some (fn [[^WeakReference reference :as entry]]
                        (when (identical? body (.get reference)) entry)) bucket)
          ^ArrayList keys
          (if entry (second entry)
            (let [;; The callback captures only the scalar hash, never BODY.
                  reference (proxy [WeakReference] [body (:queue shared-hints)] (hashCode [] key))
                  keys (ArrayList.)]
              (.add bucket [reference keys])
              (.put buckets key bucket)
              (vswap! (:size shared-hints) inc)
              keys))]
      ;; Values are weak as well: clearing a code cache must not keep its key's
      ;; opaque literals, generation, or executable code alive through this index.
      (when-not (some #(identical? canonical-key (.get ^WeakReference %)) keys)
        (when (>= (.size keys) 8) (.remove keys (int 0)))
        (.add keys (WeakReference. canonical-key)))
      (when (> @(:size shared-hints) hint-limit)
        (.clear buckets)
        (vreset! (:size shared-hints) 0)))))

(defn- matching-hint [program body]
  (some (fn [[generation lexical? direct? _ arities scalar-extension :as key]]
          (when (and (identical? generation (:generation program))
                     (= lexical? (boolean (get-in program [:options :lexical-joins])))
                     (= direct? (boolean (get-in program [:options :direct-linking])))
                     (= scalar-extension (b/runtime-block-extension-prepared (:functions program) body (:options program)))
                     ;; A caller body can survive a callee arity edit. Its cached
                     ;; region is valid only under the original key contract.
                     (every? (fn [[name arity]]
                               (= arity (when-let [f (get (:functions program) name)]
                                          (count (:params f))))) arities))
            (when-let [block (get @(:cache program) key)] [key block])))
        (hint-keys body)))

(defn- block! [program body]
  (let [^IdentityHashMap identities (:identity-dispatch program)]
    (locking identities
      (or (.get identities body)
          (when-let [[key block] (matching-hint program body)]
            (swap! (:counts program) update :cache-hits inc)
            (.put identities body block)
            (swap! (:dispatch program) assoc (nth key 3) block)
            block)
          (let [^IdentityHashMap visits (:visits program)
                n (inc (long (or (.get visits body) 0)))]
            (.put visits body n)
            (when (>= n (get-in program [:options :compile-threshold]))
              ;; Cold identities require neither content hashing nor a walk of
              ;; tail targets. Independent equivalent bodies reuse content only
              ;; here; default threshold1 preserves the original behavior.
              (let [^IdentityHashMap keys (:identity-keys program)
                    [body-key key]
                    (or (.get keys body)
                        (let [pair [(fingerprint/key body)
                                    (b/runtime-block-key-prepared (:functions program) body (:options program))]]
                          (.put keys body pair) pair))
                    cache (:cache program)
                    [canonical-key block]
                    (locking cache
                      (if-let [entry (find @cache key)]
                        (do (swap! (:counts program) update :cache-hits inc)
                            [(clojure.core/key entry) (val entry)])
                        (let [compiled (b/compile-runtime-block-prepared (:functions program) body (:options program))]
                          (swap! cache assoc key compiled)
                          (swap! (:counts program) update :compiled inc)
                          [(clojure.core/key (find @cache key)) compiled])))]
                (remember-hint! body canonical-key)
                (swap! (:dispatch program) assoc body-key block)
                (.put identities body block)
                block)))))))

(defn- cold-step! [program machine]
  (u/step! machine)
  (swap! (:counts program) update :interpreted-steps (fnil inc 0))
  machine)

(defn step-region! [program machine]
  (check! program machine)
  (when-not (= :running (u/status machine)) (m/fail "Machine is not running" {:status (u/status machine)}))
  (let [machine (b/install-runtime-context (:options program) (assoc machine :leaf-plans nil :register-layouts nil))]
    (if-let [block (block! program (u/body-of machine))]
      ((:execute! block) machine)
      (cold-step! program machine)))
  machine)

(defn run!
  ([program machine] (run! program machine 10000000))
  ([program machine fuel]
   (check! program machine)
   (when-not (and (integer? fuel) (not (neg? fuel))) (m/fail "Invalid step budget" {:fuel fuel}))
   (loop [remaining fuel machine (b/install-runtime-context (:options program) (assoc machine :leaf-plans nil :register-layouts nil))]
     (cond
       (not= :running (u/status machine)) machine
       (zero? remaining) (u/pause! machine)
       :else
       (let [block (block! program (u/body-of machine))]
         (cond
           (nil? block)
           (do (cold-step! program machine)
               (recur (dec remaining) machine))

           (>= remaining (:max-cost block))
           (let [before (u/steps machine)]
             (if-let [budget-executor (:execute-budget! block)]
               (budget-executor machine remaining)
               ((:execute! block) machine))
             (recur (- remaining (- (u/steps machine) before)) machine))
           :else (u/run! machine remaining)))))))
