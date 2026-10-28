(ns ansatz.companion-overlay
  "Pure bounded preparation of strict role companions over a captured session.
   The caller separately proves full CI overlap, missing admission and cohort
   compatibility. This neither activates a session nor upgrades legacy evidence."
  (:require [ansatz.attrs :as attrs]
            [ansatz.bundle-metadata :as metadata]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [ansatz.simp-index :as si])
  (:import [ansatz.kernel Env Name]
           [java.util ArrayDeque]
           [java.math BigInteger]
           [clojure.lang PersistentVector PersistentArrayMap PersistentHashMap PersistentHashSet BigInt]))

(def ^:private limit-keys #{:rows :items :scalar-bytes :base-items :simp-names})
(defn- fail [message data] (throw (ex-info message data)))
(defn- exact? [klass value] (identical? klass (class value)))
(defn- standard-map? [value]
  (or (exact? PersistentArrayMap value) (exact? PersistentHashMap value)))

(defn- preflight! [value charge!]
  (let [stack (ArrayDeque.)
        push! (fn [v] (charge! :items 1) (when (some? v) (.push stack v)))]
    (push! value)
    (while (not (.isEmpty stack))
      (let [v (.pop stack)]
        (cond
          (standard-map? v) (do (charge! :items (*' 2 (count v)))
                                (doseq [[k x] v]
                                  (when (some? k) (.push stack k))
                                  (when (some? x) (.push stack x))))
          (or (exact? PersistentVector v) (exact? PersistentHashSet v))
          (do (charge! :items (count v)) (doseq [x v] (when (some? x) (.push stack x))))
          (string? v) (charge! :scalar-bytes (*' 2 (.length ^String v)))
          (or (keyword? v) (boolean? v)) (charge! :scalar-bytes 8)
          (or (exact? Long v) (exact? Integer v) (exact? Short v) (exact? Byte v))
          (charge! :scalar-bytes 8)
          (or (exact? BigInteger v) (exact? BigInt v))
          (let [n (if (exact? BigInt v) (.toBigInteger ^BigInt v) v)]
            (when-not (exact? BigInteger n) (fail "Unsupported metadata integer implementation" {}))
            (charge! :scalar-bytes (max 1 (quot (+ 7 (long (.bitLength ^BigInteger n))) 8))))
          :else (fail "Unsupported strict companion payload" {}))))))

(defn- matcher-info [{:keys [numParams numDiscrs uElimPos discrs overlaps alts]}]
  {:num-params numParams :num-discrs numDiscrs :u-elim-pos uElimPos :discrs discrs
   :overlaps overlaps
   :alts (mapv (fn [{:keys [numFields numOverlaps unitThunk]}]
                 {:num-fields numFields :num-overlaps numOverlaps :unit-thunk unitThunk}) alts)})

(defn- add-attribute [charge! current {:keys [kind name target prio theorems] :as row}]
  (when (metadata/unsupported-attribute? row)
    (fail "Unsupported native attribute semantics in role overlay" {:kind kind :name name}))
  (let [target (if (= "unfold-thms" kind) theorems target)
        extension (get {"simp" :simp-lemmas "unfold" :simp-unfold "unfold-thms" :simp-unfold-thms "extern" :extern
                        "csimp" :csimp "impl" :implemented-by} kind)
        previous (env/get-extension current extension (if target {} #{}))
        priority (or prio attrs/default-simp-priority)]
    (when (contains? previous name)
      (preflight! (if target (get previous name)
                      (get (env/get-extension current :simp-priorities {}) name attrs/default-simp-priority)) charge!))
    (when (and (= "simp" kind)
               (contains? (env/get-extension current :simp-priorities {}) name)
               (not= priority (get (env/get-extension current :simp-priorities {}) name)))
      (fail "Conflicting inherited simp priority" {:name name}))
    (when (and (contains? previous name)
               (if target
                 (not= (get previous name) target)
                 (and (= "simp" kind)
                      (not= priority (get (env/get-extension current :simp-priorities {})
                                          name attrs/default-simp-priority)))))
      (fail "Conflicting inherited attribute registration" {:kind kind :name name}))
    (first (attrs/import-attr-tuples current [[kind name target (when (= "simp" kind) priority)]]
                                     {:present? (constantly true)}))))

(defn- kernel-name [^String text]
  ;; Name interning/equality can recurse through prefixes. Metadata byte bounds
  ;; alone do not cap the depth produced by a dotted declaration name.
  (loop [i 0 components 1]
    (when (> components 255) (fail "Role instance name exceeds supported Name depth" {}))
    (when (< i (.length text))
      (recur (inc i) (if (= \. (.charAt text i)) (inc components) components))))
  (name/from-string text))

(defn- instance-overlay [base rows charge!]
  (let [requested (reduce (fn [m {:keys [class name priority]}]
                            (let [key (kernel-name name)
                                  row {:class (kernel-name class) :name key :priority priority}]
                              (when-let [old (get m key)]
                                (when-not (= old row) (fail "Conflicting role instance registration" {})))
                              (if (contains? m key) m (assoc m key row)))) {} rows)
        existing (volatile! #{})]
    ;; The registry is already materialized. Scan it once within a separate
    ;; explicit budget; never discover instances by walking store declarations.
    (doseq [[class entries] base]
      (charge! :base-items 1)
      (when-not (instance? Name class) (fail "Invalid captured instance class" {}))
      (doseq [entry entries]
        (charge! :base-items 1)
        (when-not (and (map? entry) (instance? Name (:name entry))
                       (integer? (or (:priority entry) 1000))
                       (<= 0 (or (:priority entry) 1000) metadata/max-priority))
          (fail "Invalid captured instance entry" {}))
        (when-let [wanted (get requested (:name entry))]
          (when-not (and (= class (:class wanted))
                         (= (or (:priority entry) 1000) (:priority wanted)))
            (fail "Conflicting inherited instance registration" {}))
          (vswap! existing conj (:name entry)))))
    (let [additions (reduce (fn [groups {:keys [name] :as row}]
                              (let [n (kernel-name name) wanted (get requested n)]
                                (if (contains? @existing n) groups
                                    (do (vswap! existing conj n)
                                        (update groups (:class wanted) (fnil conj [])
                                                (dissoc wanted :class)))))) {} rows)]
      (reduce-kv (fn [result class entries]
                   ;; Stable priority sorting keeps base try order; role entries
                   ;; register later, with the last new equal-priority row first.
                   (assoc result class
                          (vec (sort-by #(- (or (:priority %) 1000))
                                        (concat (rseq entries) (get base class []))))))
                 base additions))))

(defn prepare-session
  "Prepare, without activation, a captured ProofContext over admitted-env and
   strict selected {:attrs :matchers :instances} row vectors. role-names is the
   exact role export's string-name set, not a union of roles or all base names.
   All references must close within it. Limits are explicit and invocation-wide:
   :rows/:items/:scalar-bytes bound metadata, :base-items the materialized instance
   registry scan, :simp-names the cumulative eager local/role lemma set.
   The caller must already establish that every role name is visible in
   admitted-env and that it extends the captured Env through strict replay.
   This function establishes neither admission nor full overlap/cohort evidence.
   The Env's instance registry is authoritative, preserving local registrations;
   captured global fallback is used only when that extension is absent."
  [captured admitted-env rows role-names limits]
  (when-not (and (map? limits) (= 5 (count limits)) (= limit-keys (set (keys limits)))
                 (every? #(and (integer? %) (pos? %) (<= % Long/MAX_VALUE)) (vals limits)))
    (fail "Explicit finite companion overlay limits required" {}))
  (when-not (and (instance? Env admitted-env) (instance? Env (:env captured))
                 (.sameExternalView ^Env admitted-env ^Env (:env captured))
                 (standard-map? rows) (= 3 (count rows)) (= metadata/roles (set (keys rows)))
                 (every? #(exact? PersistentVector %) (vals rows))
                 (exact? PersistentHashSet role-names))
    (fail "Invalid captured role overlay input" {}))
  (let [usage (volatile! {})
        charge! (fn [key n]
                  (let [total (+' (get @usage key 0) n)]
                    (when (> total (get limits key))
                      (fail "Companion overlay limit exceeded" {:limit key :actual total}))
                    (vswap! usage assoc key total)))]
    (charge! :rows (reduce +' 0 (map count (vals rows))))
    (preflight! [rows role-names] charge!)
    (doseq [[role selected] rows]
      (when-not (= (count selected) (count (metadata/select-for-names role selected role-names)))
        (fail "Companion source is outside the selected kernel role" {:role role})))
    (let [registry (or (env/get-extension admitted-env :instances nil) (:instance-index captured))]
      (when-not (map? registry) (fail "Captured session lacks a materialized instance registry" {}))
      (let [registry (instance-overlay registry (:instances rows) charge!)
            previous-eager (env/get-extension admitted-env si/eager-overlay-key #{})
            _ (when-not (exact? PersistentHashSet previous-eager)
                (fail "Captured eager simp registrations must be a standard immutable set" {}))
            _ (when (> (count previous-eager) (:simp-names limits))
                (fail "Captured eager simp overlay exceeds limit" {:limit :simp-names}))
            _ (preflight! previous-eager charge!)
            _ (when-not (every? string? previous-eager)
                (fail "Captured eager simp registrations contain a non-name" {}))
            with-attrs (reduce (partial add-attribute charge!) admitted-env (:attrs rows))
            with-matchers (reduce (fn [current {:keys [name] :as row}]
                                    (let [info (matcher-info row)
                                          previous (get (env/get-extension current :matcher-info {}) name)]
                                      (when previous
                                        (preflight! previous charge!)
                                        (when-not (= previous info)
                                          (fail "Conflicting inherited matcher registration" {:name name})))
                                      (env/update-extension current :matcher-info {} assoc name info)))
                                  with-attrs (:matchers rows))
            eager (reduce (fn [names {:keys [kind name]}]
                            (let [names (if (= "simp" kind) (conj names name) names)]
                              (when (> (count names) (:simp-names limits))
                                (fail "Companion eager simp overlay limit exceeded" {:limit :simp-names}))
                              names))
                          previous-eager (:attrs rows))
            loaded (-> with-matchers
                       (env/with-extension :instances registry)
                       (env/with-extension si/eager-overlay-key eager))]
        (assoc captured :env loaded :instance-index registry :synth-cache (atom {})
               :simp-trie nil :instance-caches {} :simp-index-caches nil
               :simp-caches {:env nil :entries {}})))))
