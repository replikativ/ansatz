(ns authenticated-raw-row-cache-v1
  "Bounded receipt-scoped source lookup policy. Cache entries contain only
   immutable owner-free row/SHA data; source authority is rechecked on every use."
  (:require [clojure.data.json :as json]
            [ansatz.research.ir.source-setup :as source]))
(def max-entries 256)
(def max-charged-bytes (* 4 1024 1024))
(def base-charge 4096)
(defn- need [ok message] (when-not ok (throw (ex-info message {:scope :authenticated-raw-row-cache-v1}))))
(defn- same-class? [klass x] (identical? klass (class x)))
(defn- name-key [value]
  ;; Flatten before encoding: no recursive conversion/hash of a deep Java Name.
  ;; Unsupported/deep/large names simply use the uncached original lookup.
  (loop [x value parts [] chars 0]
    (when (and (instance? java.util.List x) (< (count parts) 128) (<= chars 16384))
      (let [n (.size ^java.util.List x) tag (when (pos? n) (.get ^java.util.List x 0))]
        (cond
          (and (= 1 n) (= "anonymous" tag))
          (let [typed (reduce (fn [prefix [kind leaf]] [kind prefix leaf]) ["anonymous"] (rseq parts))]
            {:name typed :key (json/write-str parts)})
          (and (= 3 n) (contains? #{"str" "num"} tag))
          (let [leaf (.get ^java.util.List x 2)]
            (when (if (= "str" tag) (string? leaf)
                      (or (and (same-class? Long leaf) (<= 0 leaf))
                          (and (same-class? java.math.BigInteger leaf)
                               (not (neg? (.signum ^java.math.BigInteger leaf)))
                               (<= (.bitLength ^java.math.BigInteger leaf) 4096))
                          ;; Original exported numeric components may be strings.
                          (and (string? leaf) (<= (count leaf) 1234) (re-matches #"[0-9]+" leaf))))
              (recur (.get ^java.util.List x 1) (conj parts [tag leaf])
                     (+ chars (if (string? leaf) (count leaf) 1234)))))
          :else nil)))))
(declare immutable-charge)
(defn- children-charge [values depth budget initial]
  (loop [xs (seq values) used initial]
    (when (<= used budget)
      (if-not xs used
        (when-let [cost (immutable-charge (first xs) depth (- budget used))]
          (recur (next xs) (+ used cost)))))))
(defn- immutable-charge [x depth budget]
  ;; Exact classes exclude mutable/proxy collection implementations, SubVector
  ;; backing retention, sorted-map comparators, and metadata-held owner aliases.
  ;; Charges deliberately overcount shared values and collection slots. This is
  ;; a conservative storage estimate, not a measurement/hard JVM-heap bound.
  (when (and (<= depth 64) (pos? budget))
    (let [cost
          (cond
            (nil? x) 16
            (string? x) (+ 80 (* 2 (count x)))
            (or (same-class? Long x) (same-class? Integer x) (same-class? Short x)
                (same-class? Byte x) (same-class? Boolean x) (same-class? Double x)) 64
            (same-class? java.math.BigInteger x) (+ 96 (* 8 (quot (+ 31 (.bitLength ^java.math.BigInteger x)) 32)))
            (and (same-class? clojure.lang.PersistentVector x) (nil? (meta x)))
            (children-charge x (inc depth) budget (+ 128 (* 64 (count x))))
            (and (or (same-class? clojure.lang.PersistentArrayMap x) (same-class? clojure.lang.PersistentHashMap x))
                 (nil? (meta x)))
            (when (every? string? (keys x))
              (children-charge (mapcat identity x) (inc depth) budget (+ 128 (* 1024 (count x)))))
            :else nil)]
      (when (and cost (<= cost budget)) cost))))
(defn- state! [cell]
  (let [s @cell]
    (need (not (:closed s)) "Raw-row cache is closed")
    (need (identical? (:thread s) (Thread/currentThread)) "Raw-row cache is thread confined") s))
(defn- guard! [cell driver]
  (source/guard-source! (:receipt (state! cell)) (:source driver)))
(defn- evict-to-fit [state charge]
  (loop [s state]
    (if (and (< (count (:entries s)) (:entry-limit s))
             (<= (+ (:bytes s) charge) (:byte-limit s))) s
      (let [[key entry] (apply min-key (comp :stamp val) (:entries s))]
        (recur (-> s (update :entries dissoc key) (update :bytes - (:charge entry)) (update :evictions inc)))))))
(defn- resolve! [cell driver name]
  (guard! cell driver)
  (try
    (let [key (name-key name) cached (when key (get-in @cell [:entries (:key key)]))]
      (if cached
        (do (swap! cell (fn [s] (let [tick (inc (:clock s))]
                                 (-> s (assoc :clock tick) (assoc-in [:entries (:key key) :stamp] tick) (update :hits inc)))))
            {:row (:row cached) :sha256 (:sha256 cached) :source-binding (:source driver)})
        (let [_ (swap! cell update :misses inc)
              ;; CodeReceipt selects the fixed original+overlay scope; there is
              ;; no arbitrary caller resolver or per-driver substitution here.
              entry (source/lookup-entry (:receipt (state! cell)) name)
              _ (assert entry "Original declaration absent from authenticated source")
              {:keys [row sha256]} entry
              budget (- (:byte-limit @cell) base-charge)
              row-charge (when (and key (string? sha256) (re-matches #"[0-9a-f]{64}" sha256))
                           (immutable-charge row 0 budget))
              charge (when (and row-charge (map? row) (= (:name key) (get row "name")))
                       (+ 512 192 (* 2 (count (:key key))) row-charge))]
          (if (and charge (<= charge budget))
            (swap! cell
              (fn [s]
                (let [s (evict-to-fit s charge) tick (inc (:clock s))]
                  (-> s (assoc :clock tick) (assoc-in [:entries (:key key)] {:row row :sha256 sha256 :charge charge :stamp tick})
                      (update :bytes + charge) (update :insertions inc)))))
            (swap! cell update :uncached inc))
          {:row row :sha256 sha256 :source-binding (:source driver)})))
    (finally (guard! cell driver))))
(defn open-policy
  "Create one injected resolver policy for THIS actual CodeReceipt. Unknown Names
   retain the original fixed-source lookup/assert behavior and are never cached.
   The receipt is an actual existing opaque capability, not a descriptive map."
  ([receipt] (open-policy receipt {}))
  ([receipt {:keys [entry-limit byte-limit] :or {entry-limit max-entries byte-limit max-charged-bytes}}]
   (need (and (integer? entry-limit) (<= 1 entry-limit max-entries)
              (integer? byte-limit) (<= (+ base-charge 1024) byte-limit max-charged-bytes)) "Cache bounds exceed profile")
   (let [cell (atom {:receipt receipt :thread (Thread/currentThread) :closed false :entries {}
                     :entry-limit entry-limit :byte-limit byte-limit :bytes base-charge :clock 0
                     :hits 0 :misses 0 :uncached 0 :evictions 0 :insertions 0})]
     {:resolve-row! (fn [driver name] (resolve! cell driver name))
      :check-source! (fn [driver] (guard! cell driver))
      :stats (fn [] (let [s @cell] (assoc (select-keys s [:closed :hits :misses :uncached :evictions :insertions :bytes :byte-limit :entry-limit])
                                        :entries (count (:entries s)))))
      :close! (fn [] (when-not (:closed @cell)
                      (state! cell)
                      ;; Drop both row data and receipt anchors; never close the
                      ;; caller-owned source/catalogue/engine resources.
                      (reset! cell {:closed true :entries {}})) nil)})))
