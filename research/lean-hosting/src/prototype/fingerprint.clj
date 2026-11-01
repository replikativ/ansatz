(ns prototype.fingerprint
  "Stack-safe Merkle SHA256 keys for normalized IR. Map/set order and metadata
   are ignored, matching Clojure collection equality; record classes and number
   representations remain distinct. Opaque literals use exact object identity.
   A bounded identity-root cache makes repeated keys O(1), without hashing IR."
  (:refer-clojure :exclude [key])
  (:import [java.security MessageDigest]
           [java.util LinkedHashMap]
           [java.math BigInteger BigDecimal]
           [clojure.lang BigInt Ratio]))

(deftype IdentityKey [value]
  Object
  (equals [_ other] (and (instance? IdentityKey other)
                         (identical? value (.-value ^IdentityKey other))))
  (hashCode [_] (System/identityHashCode value))
  (toString [_] "<opaque-identity>"))

(def ^:private root-limit 4096)
(defonce ^:private root-cache
  {:lock (Object.) :entries (LinkedHashMap. 64 (float 0.75) true)
   :metrics (atom {:hits 0 :misses 0})})

(defn clear-cache! []
  (locking (:lock root-cache)
    (.clear ^LinkedHashMap (:entries root-cache))
    (reset! (:metrics root-cache) {:hits 0 :misses 0}))
  nil)

(defn cache-stats []
  (locking (:lock root-cache)
    (assoc @(:metrics root-cache) :entries (.size ^LinkedHashMap (:entries root-cache)) :limit root-limit)))

(defn- update-string! [^MessageDigest digest ^String s]
  ;; Encode UTF16 code units directly. Charset encoders replace malformed lone
  ;; surrogates, which would merge distinct literal Strings into the same key.
  (let [n (.length s) bytes (byte-array (+ 4 (* 2 n)))]
    (dotimes [i 4] (aset-byte bytes i (unchecked-byte (unsigned-bit-shift-right n (* 8 (- 3 i))))))
    (dotimes [i n]
      (let [c (int (.charAt s i)) offset (+ 4 (* 2 i))]
        (aset-byte bytes offset (unchecked-byte (unsigned-bit-shift-right c 8)))
        (aset-byte bytes (inc offset) (unchecked-byte c))))
    (.update digest bytes)))

(defn- digest [tag parts]
  (let [d (MessageDigest/getInstance "SHA-256")]
    (update-string! d "ansatz-ir-merkle/1")
    (update-string! d tag)
    (doseq [part parts] (update-string! d part))
    (let [bytes (.digest d) result (char-array 64) alphabet "0123456789abcdef"]
      (dotimes [i 32]
        (let [b (bit-and 255 (aget bytes i))]
          (aset-char result (* 2 i) (.charAt alphabet (unsigned-bit-shift-right b 4)))
          (aset-char result (inc (* 2 i)) (.charAt alphabet (bit-and 15 b)))))
      (String. result))))

(defn- number-parts [value]
  (when (contains? #{Byte Short Integer Long Float Double BigInteger BigDecimal BigInt Ratio} (class value))
    [(.getName (class value))
     (cond (instance? Double value) (Long/toHexString (Double/doubleToRawLongBits value))
           (instance? Float value) (Integer/toHexString (Float/floatToRawIntBits value))
           :else (.toString ^Object value))]))

(defn- primitive-digest [value]
  (cond
    (nil? value) (digest "nil" [])
    (true? value) (digest "boolean" ["true"])
    (false? value) (digest "boolean" ["false"])
    (string? value) (digest "string" [value])
    (keyword? value) (digest "keyword" [(if (some? (namespace value)) "ns" "none")
                                       (or (namespace value) "") (name value)])
    (symbol? value) (digest "symbol" [(if (some? (namespace value)) "ns" "none")
                                     (or (namespace value) "") (name value)])
    (char? value) (digest "character" [(str (int value))])
    (number? value) (when-let [parts (number-parts value)] (digest "number" parts))))

(defn- calculate [root]
  (loop [work [[:visit root]] results [] opaque #{}]
    (if (empty? work)
      [(peek results) opaque]
      (let [[operation value extra] (peek work) work (pop work)]
        (if (= operation :finish)
          (let [n value offset (- (count results) n) children (subvec results offset)
                results (subvec results 0 offset)
                [kind class-name] extra
                parts (case kind
                        (:map :record) (sort (map #(digest "entry" %) (partition 2 children)))
                        :set (sort children)
                        children)
                parts (if class-name (cons class-name parts) parts)]
            (recur work (conj results (digest (name kind) parts)) opaque))
          (if-let [primitive (primitive-digest value)]
            (recur work (conj results primitive) opaque)
            (let [kind (cond (record? value) :record (map? value) :map (vector? value) :vector
                             (set? value) :set (sequential? value) :list)
                  children (when kind (if (contains? #{:map :record} kind)
                                        (into [] (mapcat (fn [[k v]] [k v])) value) (vec value)))]
              (if kind
                (let [record-class (when (= kind :record) (class value))
                      ;; Class identity matters across classloader/reload boundaries.
                      class-name (when record-class (.getName ^Class record-class))
                      work (conj work [:finish (count children) [kind class-name]])
                      work (reduce #(conj %1 [:visit %2]) work (rseq children))]
                  (recur work results (cond-> opaque record-class (conj (IdentityKey. record-class)))))
                (recur work
                       (conj results (digest "opaque" [(.getName (class value))
                                                        (str (System/identityHashCode value))]))
                       (conj opaque (IdentityKey. value)))))))))))

(defn uncached-key
  "Calculate a complete fingerprint without retaining its input in the root cache.
   Callers traversing DAGs must memoize nodes themselves before using this on
   child-digest envelopes; this generic calculation does not deduplicate DAGs."
  [value]
  (calculate value))

(defn key
  "Return [SHA256 opaque-identities]. Independent equivalent parses match;
   opaque literals match only when their actual JVM objects are identical.
   Record class names enter the digest; Class identity guards the companion set
   against classloader/reload confusion. Complete keys are JVM-local when such
   identity guards occur; plain data digests are deterministic across processes.
   Do not extract the digest alone: the identity component disambiguates even
   System.identityHashCode collisions. Cyclic Java collections are opaque."
  [value]
  (let [identity (IdentityKey. value)
        cached (locking (:lock root-cache)
                 (let [result (.get ^LinkedHashMap (:entries root-cache) identity)]
                   (swap! (:metrics root-cache) update (if result :hits :misses) inc)
                   result))]
    (or cached
        (let [result (calculate value)]
          (locking (:lock root-cache)
            (let [entries ^LinkedHashMap (:entries root-cache)]
              (.put entries identity result)
              (when (> (.size entries) root-limit)
                (let [iterator (.iterator (.entrySet entries))]
                  (.next iterator) (.remove iterator)))))
          result))))
