(ns prototype.runtime-string
  "Immutable host strings with Lean UTF-8 byte positions, not UTF-16 offsets.
   Profile: pinned Lean 4.33.1 x86_64; lean.h string primitives and mixHash,
   runtime/object.cpp UTF8 helpers, runtime/hash.cpp MurmurHash64A (seed 11).
   Native C oracle verifies hashes, ordering tags, invalid positions and extraction.
   Lone UTF-16 surrogates are rejected. No pointer identity/capacity/reuse claim.
   Full 64-bit hashing is JVM-only; JS fails explicitly rather than truncating.
   A bounded derived-view cache is shared safely across worlds. It stores no
   guest state/references; its byte budget counts UTF8 input, not JVM heap size.
   Append/push use separate bounded Unicode-validity hints, without UTF8 views."
  (:require [prototype.native-scalar :as native])
  #?(:clj (:import [java.util LinkedHashMap] [java.lang.ref WeakReference])))

(def supported-symbols
  (assoc (into {} (map (fn [[symbol arity]] [symbol {:arity arity}])
                {"lean_string_utf8_at_end" 2 "lean_string_utf8_next" 2
                 "lean_string_utf8_next_fast" 3 "lean_string_utf8_get" 2
                 "lean_string_utf8_get_fast" 3 "lean_string_get_byte_fast" 3
                 "lean_string_is_valid_pos" 2 "lean_string_utf8_extract" 3
                 "lean_string_utf8_byte_size" 1 "lean_string_length" 1
                 "lean_string_compare" 2 "lean_string_dec_eq" 2 "lean_string_dec_lt" 2
                 "lean_string_hash" 1 "lean_uint64_mix_hash" 2
                 "lean_string_memcmp" 7 "lean_string_append" 2 "lean_string_push" 2
                 "lean_string_contains" 2 "lean_string_posof" 2
                 "lean_string_mk" 1 "lean_string_of_usize" 1 "lean_string_validate_utf8" 1 "lean_string_from_utf8_unchecked" 2
                 "lean_substring_beq" 2}))
         "lean_string_utf8_set" {:arity 4 :arities #{3 4}}))

(defn- fail [message data] (throw (ex-info message data)))
(defn- nat! [x]
  (native/nat-value x))

(defn valid-utf8?
  "Pinned runtime/utf8.cpp validate_utf8_one. Accept NUL/noncharacters; reject
   bad/truncated continuations, overlong encodings, surrogates and >U+10FFFF."
  [bytes]
  (when-not (and (vector? bytes) (every? #(and (integer? %) (<= 0 % 255)) bytes))
    (fail "Malformed guest ByteArray storage" {}))
  (loop [position 0]
    (if (= position (count bytes)) true
      (let [lead (nth bytes position)
            width (cond (< lead 128) 1 (= 192 (bit-and lead 224)) 2
                        (= 224 (bit-and lead 240)) 3 (= 240 (bit-and lead 248)) 4 :else 0)]
        (if (or (zero? width) (> (+ position width) (count bytes))) false
          (let [cp (loop [j 1 cp (bit-and lead (case width 1 127 2 31 3 15 4 7))]
                     (if (= j width) cp
                       (let [byte (nth bytes (+ position j))]
                         (if (= 128 (bit-and byte 192))
                           (recur (inc j) (+ (* cp 64) (bit-and byte 63))) -1))))]
            (if (or (neg? cp) (< cp (case width 1 0 2 128 3 2048 4 65536))
                    (<= 55296 cp 57343) (> cp 1114111)) false
              (recur (+ position width)))))))))

(defn string-value
  "Contextual String view preserving the identity of a heap carrier."
  [ops world value]
  (if (string? value) value
    (let [node (when (and (:ref? ops) ((:ref? ops) value)) ((:node ops) world value))]
      (when-not (and (= :string (:kind node)) (string? (:text node)))
        (fail "Expected guest String carrier" {:value value}))
      (:text node))))
(defn- code-unit [s i] #?(:clj (int (.charAt ^String s (int i))) :cljs (.charCodeAt s i)))
(defn- char-string [cp]
  (when-not (and (integer? cp) (<= 0 cp 1114111) (not (<= 55296 cp 57343)))
    (fail "Invalid Unicode scalar value" {:value cp}))
  #?(:clj (String. (Character/toChars (int cp))) :cljs (js/String.fromCodePoint cp)))

(def ^:private validation-entry-limit 64)
(def ^:private validation-unit-budget 2097152)
;; Retain the original Var and its WeakReference-only representation for old
;; functions already executing while this namespace is hot-reloaded. New code
;; uses a distinct atom; changing only the entry reader is not sufficient.
(defonce ^:private validation-cache
  (atom {:entries [] :hits 0 :scans 0 :input-code-units 0}))
(swap! validation-cache update :entries
  (fn [entries]
    (into [] (keep #?(:clj #(if (instance? WeakReference %) % (:reference %))
                     :cljs #(if (string? %) % (:string %)))) entries)))

(defonce ^:private summary-cache
  (atom {:entries [] :hits 0 :scans 0 :input-code-units 0}))

(defn clear-validation-cache!
  "Drop Unicode validity hints. No guest values/state are changed. JVM hints are
   weak identity references; JS primitive-string hints have a 2 Mi UTF16 budget."
  [] (reset! summary-cache {:entries [] :hits 0 :scans 0 :input-code-units 0}) nil)

(defn validation-cache-stats
  "Diagnostics: validation input length counts misses, not string copying.
   JVM cache entries do not retain their strings. No content hashes are computed."
  []
  (let [state @summary-cache]
    (assoc (dissoc state :entries) :entries (count (:entries state))
           :entry-limit validation-entry-limit
           :retention #?(:clj :weak-identity :cljs :bounded-string-values)
           :retained-code-units #?(:clj 0 :cljs (reduce + 0 (map #(count (if (string? %) % (:string %))) (:entries state)))))))

(defn- cached-validity [s]
  (let [hit (some #?(:clj #(let [^WeakReference reference (if (instance? WeakReference %) % (:reference %))]
                              (when (identical? s (.get reference)) %))
                    ;; JS strings are primitive immutable values, not WeakMap
                    ;; keys. Length first avoids comparing growing prefixes.
                    ;; Accept older hint entries when hot-reloading this source.
                    :cljs #(let [text (if (string? %) % (:string %))]
                             (when (and (= (count s) (count text)) (identical? s text)) %)))
                  (:entries @summary-cache))]
    (when hit (swap! summary-cache update :hits inc))
    hit))

(defn- remember-valid!
  ([s] (remember-valid! s nil))
  ([s summary]
  (swap! summary-cache update :entries
    (fn [entries]
      #?(:clj (into [{:reference (WeakReference. s) :summary summary}] (take (dec validation-entry-limit) entries))
         :cljs
         (if (> (count s) validation-unit-budget) entries
           (loop [pending (cons {:string s :summary summary} entries) retained [] units 0]
             (if-let [entry (first pending)]
               (let [text (if (string? entry) entry (:string entry))]
                 (if (or (= (count retained) validation-entry-limit)
                         (> (+ units (count text)) validation-unit-budget)) retained
                   (recur (next pending) (conj retained entry) (+ units (count text)))))
               retained))))))
  s))

(defn- scalar-byte-width [cp]
  (cond (< cp 128) 1 (< cp 2048) 2 (< cp 65536) 3 :else 4))

(defn- concatenate [a b]
  ;; Both are already validated immutable strings. String.concat allocates just
  ;; the resulting string, without str's intermediate StringBuilder buffer.
  #?(:clj (.concat ^String a ^String b) :cljs (str a b)))

(defn- string-summary! [s]
  (when-not (string? s) (fail "Expected immutable guest string" {:value s}))
  (or (:summary (cached-validity s))
   (do
    (swap! summary-cache #(-> % (update :scans inc) (update :input-code-units + (count s))))
    ;; Count and validate without allocating any UTF8 bytes, position map, or
    ;; character vector. Native strings cache exactly these two header counts.
    (let [summary
     (loop [i 0 byte-size 0 length 0]
      (if (= i (count s)) {:byte-size byte-size :length length}
        (let [u (code-unit s i)]
          (cond
            (<= 55296 u 56319)
            (if (and (< (inc i) (count s)) (<= 56320 (code-unit s (inc i)) 57343))
              (recur (+ i 2) (+ byte-size 4) (inc length)) (fail "Malformed host Unicode string" {:offset i}))
            (<= 56320 u 57343) (fail "Malformed host Unicode string" {:offset i})
            :else (recur (inc i) (+ byte-size (scalar-byte-width u)) (inc length))))))]
      (remember-valid! s summary)
      summary))))

(defn from-utf8
  "Decode proven-valid UTF8. Invalid proof inputs fail before producing a host
   String; Java's replacement-character decoding is never used."
  [bytes]
  (when-not (valid-utf8? bytes) (fail "UTF8 proof violated for unchecked String construction" {}))
  (loop [i 0 parts []]
    (if (= i (count bytes)) (remember-valid! (apply str parts) {:byte-size (count bytes) :length (count parts)})
      (let [lead (nth bytes i)
            width (cond (< lead 128) 1 (< lead 224) 2 (< lead 240) 3 :else 4)
            cp (loop [j 1 cp (bit-and lead (case width 1 127 2 31 3 15 4 7))]
                 (if (= j width) cp
                   (recur (inc j) (+ (* cp 64) (bit-and 63 (nth bytes (+ i j)))))))]
        (recur (+ i width) (conj parts (char-string cp)))))))

(defn- encode-string [s]
  (when-not (string? s) (fail "Expected immutable guest string" {:value s}))
  (loop [i 0 bytes [] starts {} chars []]
    (if (= i (count s)) (do (remember-valid! s {:byte-size (count bytes) :length (count chars)})
                           {:string s :bytes bytes :starts starts :chars chars})
      (let [u (code-unit s i)
            high? (<= 55296 u 56319)
            low? (<= 56320 u 57343)
            v (when (and high? (< (inc i) (count s))) (code-unit s (inc i)))
            cp (cond (and high? v (<= 56320 v 57343)) (+ 65536 (* (- u 55296) 1024) (- v 56320))
                     (or high? low?) (fail "Malformed host Unicode string" {:offset i})
                     :else u)
            encoded (cond (< cp 128) [cp]
                          (< cp 2048) [(+ 192 (quot cp 64)) (+ 128 (mod cp 64))]
                          (< cp 65536) [(+ 224 (quot cp 4096)) (+ 128 (mod (quot cp 64) 64)) (+ 128 (mod cp 64))]
                          :else [(+ 240 (quot cp 262144)) (+ 128 (mod (quot cp 4096) 64))
                                 (+ 128 (mod (quot cp 64) 64)) (+ 128 (mod cp 64))])]
        (recur (+ i (if high? 2 1)) (into bytes encoded)
               (assoc starts (count bytes) {:cp cp :offset i}) (conj chars cp))))))

(def ^:dynamic *encoding-cache-byte-budget*
  "UTF8 input bytes retained by the derived-view cache; capped at 4 MiB.
   Clear the cache before binding a smaller limit for deterministic budget tests."
  4194304)
(def ^:private cache-entry-limit 8)
(defonce ^:private encoding-cache
  {:entries #?(:clj (LinkedHashMap. 8 (float 0.75) true) :cljs (js/Map.))
   :lock #?(:clj (Object.) :cljs nil)
   :metrics (atom {:bytes 0 :hits 0 :misses 0})})

(defn clear-encoding-cache!
  "Drop derived encodings and diagnostic counters; guest behavior is unchanged."
  []
  #?(:clj (locking (:lock encoding-cache)
            (.clear ^LinkedHashMap (:entries encoding-cache))
            (reset! (:metrics encoding-cache) {:bytes 0 :hits 0 :misses 0}))
     :cljs (do (.clear (:entries encoding-cache))
               (reset! (:metrics encoding-cache) {:bytes 0 :hits 0 :misses 0})))
  nil)

(defn encoding-cache-stats
  "Diagnostics only. `:bytes` sums UTF8 input lengths, excluding derived overhead."
  []
  #?(:clj (locking (:lock encoding-cache)
            (assoc @(:metrics encoding-cache) :entries (.size ^LinkedHashMap (:entries encoding-cache))
                   :entry-limit cache-entry-limit :byte-budget (min 4194304 *encoding-cache-byte-budget*)))
     :cljs (assoc @(:metrics encoding-cache) :entries (.-size (:entries encoding-cache))
                  :entry-limit cache-entry-limit :byte-budget (min 4194304 *encoding-cache-byte-budget*))))

(defn- cache-read [s]
  #?(:clj (locking (:lock encoding-cache)
            (let [value (.get ^LinkedHashMap (:entries encoding-cache) s)]
              (swap! (:metrics encoding-cache) update (if value :hits :misses) inc)
              value))
     :cljs (let [entries (:entries encoding-cache) value (.get entries s)]
             (swap! (:metrics encoding-cache) update (if value :hits :misses) inc)
             (when value (.delete entries s) (.set entries s value))
             value)))

(defn- cache-write [s encoded]
  (let [budget (max 0 (min 4194304 *encoding-cache-byte-budget*))
        cost (count (:bytes encoded))]
    (when (<= cost budget)
      #?(:clj
         (locking (:lock encoding-cache)
           (let [entries ^LinkedHashMap (:entries encoding-cache)]
             ;; Another thread may have computed the same view after our miss.
             (when-not (.containsKey entries s)
               (.put entries s encoded)
               (swap! (:metrics encoding-cache) update :bytes + cost))
             (loop []
               (when (or (> (.size entries) cache-entry-limit) (> (:bytes @(:metrics encoding-cache)) budget))
                 (let [iterator (.iterator (.entrySet entries)) entry (.next iterator)]
                   (swap! (:metrics encoding-cache) update :bytes - (count (:bytes (.getValue entry))))
                   (.remove iterator))
                 (recur)))))
         :cljs
         (let [entries (:entries encoding-cache)]
           (when-not (.has entries s)
             (.set entries s encoded)
             (swap! (:metrics encoding-cache) update :bytes + cost))
           (loop []
             (when (or (> (.-size entries) cache-entry-limit) (> (:bytes @(:metrics encoding-cache)) budget))
               (let [key (.-value (.next (.keys entries))) value (.get entries key)]
                 (.delete entries key)
                 (swap! (:metrics encoding-cache) update :bytes - (count (:bytes value))))
               (recur)))))))
  encoded)

(defn- encoding [s]
  (when-not (string? s) (fail "Expected immutable guest string" {:value s}))
  ;; Java String caches its hash; LinkedHashMap avoids Clojure's repeated string
  ;; hash traversal on each character primitive. JS Map uses native string keys.
  (or (cache-read s) (cache-write s (encode-string s))))

(defn- valid-pos? [encoded p]
  (or (= p (count (:bytes encoded))) (contains? (:starts encoded) p)))
(defn- byte-width [b]
  (cond (< b 128) 1 (<= 192 b 223) 2 (<= 224 b 239) 3 (<= 240 b 247) 4 :else 1))
(defn- plus-one [p] #?(:clj (inc' p) :cljs (nat! (inc p))))
(defn- advance [encoded p]
  (if (< p (count (:bytes encoded)))
    (+ p (byte-width (nth (:bytes encoded) (int p)))) (plus-one p)))
(defn- fast-pos! [encoded p]
  (when-not (< p (count (:bytes encoded)))
    (fail "Fast UTF8 primitive precondition violated" {:position p :size (count (:bytes encoded))})) p)
(defn- substring-host [s b e]
  #?(:clj (.substring ^String s (int b) (int e)) :cljs (.substring s b e)))
(defn- extract [encoded b e]
  (let [s (:string encoded) size (count (:bytes encoded))]
    ;; Preserve the native implementation's large-Nat branch, even when a huge
    ;; begin index would otherwise imply an empty mathematical slice.
    (cond #?(:clj (or (> b 9223372036854775807N) (> e 9223372036854775807N)) :cljs false) s
          (or (>= b e) (>= b size) (not (valid-pos? encoded b))) ""
          :else (let [e (if (or (> e size) (not (valid-pos? encoded e))) size e)
                      end-offset (if (= e size) (count s) (get-in encoded [:starts e :offset]))]
                  (substring-host s (get-in encoded [:starts b :offset]) end-offset)))))
(defn- compare-bytes [a b]
  (loop [i 0]
    (if (= i (min (count a) (count b))) (compare (count a) (count b))
      (let [c (compare (nth a i) (nth b i))] (if (zero? c) (recur (inc i)) c)))))

#?(:clj
   (do
     (def ^:private modulus 18446744073709551616N)
     (def ^:private multiplier 14313749767032793493N)
     (defn- u64 [x] (mod x modulus))
     (defn- xor64 [a b] (bigint (.xor (biginteger a) (biginteger b))))
     (defn- shr47 [a] (bigint (.shiftRight (biginteger a) 47)))
     (defn- times-m [a] (u64 (*' a multiplier)))
     (defn- little-word [bytes] (reduce (fn [n b] (+' (*' n 256) b)) 0 (rseq (vec bytes))))
     (defn- hash-bytes [bytes]
       (let [full (* 8 (quot (count bytes) 8))
             h (loop [i 0 h (xor64 11 (times-m (count bytes)))]
                 (if (= i full) h
                   (let [k (times-m (little-word (subvec bytes i (+ i 8))))
                         k (times-m (xor64 k (shr47 k)))]
                     (recur (+ i 8) (times-m (xor64 h k))))))
             h (if (< full (count bytes))
                 (times-m (xor64 h (little-word (subvec bytes full)))) h)
             h (times-m (xor64 h (shr47 h)))]
         (xor64 h (shr47 h))))
     (defn- mix-hash [h k]
       (doseq [x [h k]]
         (when-not (and (integer? x) (<= 0 x) (< x modulus))
           (fail "Expected UInt64 hash input" {:value x})))
       (let [k (times-m k) k (xor64 k (shr47 k)) k (xor64 k multiplier)]
         (times-m (xor64 h k))))))

(defn- hash-unsupported [] (fail "Full UInt64 string hashing requires an exact 64-bit backend" {}))

(defn- raw-substring [ops world value]
  (let [node ((:node ops) world value) fields (vec (:fields node))]
    (when-not (and (= :ctor (:kind node)) (= 3 (count fields)))
      (fail "Malformed guest raw substring" {:node node}))
    (let [[s b e] fields encoded (encoding (string-value ops world s)) size (count (:bytes encoded))
          b (native/nat-value ops world b) e (native/nat-value ops world e)
          b (if (valid-pos? encoded b) b size) e (if (valid-pos? encoded e) e size)]
      (subvec (:bytes encoded) (int b) (int (max b e))))))

(defn- evaluate-flat
  "Raw extern evaluator, retaining erased proof positions from exported IR.
   Strings are immutable host values; owning string args need no logical release.
   Heap-backed list/substring arguments are consumed through injected release."
  [ops world symbol args]
  (let [spec (get supported-symbols symbol)]
    (when-not spec (fail "Unsupported string runtime extern" {:symbol symbol}))
    (when-not (= (:arity spec) (count args)) (fail "String runtime arity mismatch" {:symbol symbol})))
  (let [[a b c d e] args]
    (cond
      (= symbol "lean_string_from_utf8_unchecked")
      (let [node (when ((:ref? ops) a) ((:node ops) world a))]
        (when-not (and (= :byte-array (:kind node)) (empty? (:fields node)))
          (fail "Expected guest ByteArray for String construction" {:value a}))
        (let [text (from-utf8 (:bytes node))]
          [((:release ops) world a 1) text]))
      (= symbol "lean_string_validate_utf8")
      (let [node (when ((:ref? ops) a) ((:node ops) world a))]
        (when-not (and (= :byte-array (:kind node)) (empty? (:fields node)))
          (fail "Expected guest ByteArray for UTF8 validation" {:value a}))
        [world (if (valid-utf8? (:bytes node)) 1 0)])
      (= symbol "lean_uint64_mix_hash") [world #?(:clj (mix-hash a b) :cljs (hash-unsupported))]
      (= symbol "lean_string_utf8_byte_size") [world (:byte-size (string-summary! a))]
      (= symbol "lean_string_length") [world (:length (string-summary! a))]
      (= symbol "lean_string_append")
      (let [left (string-summary! a) right (string-summary! b)]
        [world (remember-valid! (concatenate a b)
                 {:byte-size (+ (:byte-size left) (:byte-size right))
                  :length (+ (:length left) (:length right))})])
      (= symbol "lean_string_push")
      (let [summary (string-summary! a) cp (char-string b)]
        [world (remember-valid! (concatenate a cp)
                 {:byte-size (+ (:byte-size summary) (scalar-byte-width b))
                  :length (inc (:length summary))})])
      (= symbol "lean_string_of_usize")
      (do (nat! a)
          (when #?(:clj (> a 18446744073709551615N) :cljs false) (fail "Expected USize" {:value a}))
          (let [s (str a)] [world (remember-valid! s {:byte-size (count s) :length (count s)})]))
      (= symbol "lean_string_mk")
      (let [s (loop [value a result ""]
                (if ((:ref? ops) value)
                  (let [node ((:node ops) world value) [head tail] (:fields node)]
                    (when-not (and (= :ctor (:kind node)) (= 1 (:tag node)) (= 2 (count (:fields node))))
                      (fail "Malformed guest character list" {:node node}))
                    (recur tail (str result (char-string (native/unsigned-value 32 (native/number-value ops world head))))))
                  (if (or (= value 0) (= (:tag value) 0) (and (native/native-scalar? value) (zero? (native/payload value)))) result
                    (fail "Malformed character list terminator" {:value value}))))]
        [((:release ops) world a 1) (remember-valid! s)])
      (= symbol "lean_substring_beq")
      (let [result (if (= (raw-substring ops world a) (raw-substring ops world b)) 1 0)]
        [((:release ops) ((:release ops) world a 1) b 1) result])
      :else
      (let [encoded (encoding a) bytes (:bytes encoded) size (count bytes)]
        [world
         (case symbol
           "lean_string_hash" #?(:clj (hash-bytes bytes) :cljs (hash-unsupported))
           "lean_string_contains" (do (char-string b) (if (some #{b} (:chars encoded)) 1 0))
           "lean_string_posof"
           ;; Init/Data/String/Search.lean Internal.posOfImpl exports
           ;; (s.find c).offset: first matching UTF8 byte position, else end.
           ;; Positions refer to scalar boundaries, including embedded NUL.
           (do (char-string b)
               (reduce-kv (fn [found position entry]
                            (if (= b (:cp entry)) (min found position) found))
                          size (:starts encoded)))
           ("lean_string_compare" "lean_string_dec_eq" "lean_string_dec_lt")
           (let [comparison (compare-bytes bytes (:bytes (encoding b)))]
             (case symbol "lean_string_compare" (cond (neg? comparison) 0 (zero? comparison) 1 :else 2)
                          "lean_string_dec_eq" (if (zero? comparison) 1 0)
                          "lean_string_dec_lt" (if (neg? comparison) 1 0)))
           "lean_string_memcmp"
           (let [other (:bytes (encoding b)) l (nat! c) r (nat! d) n (nat! e)]
             (when-not (and (<= l size) (<= r (count other)) (<= n (- size l)) (<= n (- (count other) r)))
               (fail "String memcmp precondition violated" {:left l :right r :length n}))
             (if (= (subvec bytes (int l) (int (+ l n))) (subvec other (int r) (int (+ r n)))) 1 0))
           "lean_string_utf8_extract" (remember-valid! (extract encoded (nat! b) (nat! c)))
           "lean_string_utf8_at_end" (if (>= (nat! b) size) 1 0)
           "lean_string_is_valid_pos" (if (valid-pos? encoded (nat! b)) 1 0)
           "lean_string_utf8_next" (advance encoded (nat! b))
           "lean_string_utf8_next_fast" (advance encoded (fast-pos! encoded (nat! b)))
           "lean_string_get_byte_fast" (nth bytes (int (fast-pos! encoded (nat! b))))
           "lean_string_utf8_get" (get-in encoded [:starts (nat! b) :cp] 65)
           "lean_string_utf8_get_fast" (get-in encoded [:starts (fast-pos! encoded (nat! b)) :cp] 65))]))))


(def ^:private two-string-symbols
  #{"lean_string_append" "lean_string_compare" "lean_string_dec_eq" "lean_string_dec_lt" "lean_string_memcmp"})
(def ^:private non-string-first-symbols
  #{"lean_uint64_mix_hash" "lean_string_of_usize" "lean_string_mk" "lean_substring_beq" "lean_string_validate_utf8" "lean_string_from_utf8_unchecked"})
(def ^:private position-symbols
  #{"lean_string_utf8_extract" "lean_string_utf8_at_end" "lean_string_is_valid_pos"
    "lean_string_utf8_next" "lean_string_utf8_next_fast" "lean_string_get_byte_fast"
    "lean_string_utf8_get" "lean_string_utf8_get_fast"})
(def ^:private character-symbols
  #{"lean_string_push" "lean_string_contains" "lean_string_posof"})

(defn- set-utf8 [ops world args]
  ;; runtime/object.cpp:2468–2495: only unique ASCII→ASCII updates in place.
  ;; Invalid positions transfer the SAME owner, including boxed Nat positions.
  (when-not (contains? #{3 4} (count args))
    (fail "String runtime arity mismatch" {:symbol "lean_string_utf8_set" :arity (count args)}))
  (let [[source position cp] args
        text (string-value ops world source)
        position-value (native/nat-value ops world position)
        cp (native/unsigned-value 32 (native/number-value ops world cp))
        encoded (encoding text)
        boxed-position? (or (and (:ref? ops) ((:ref? ops) position))
                           #?(:clj (> position-value 9223372036854775807N) :cljs false))
        entry (when-not boxed-position? (get (:starts encoded) position-value))]
    (if-not entry [world source]
      (let [replacement (char-string cp)
            offset (:offset entry)
            end (+ offset (if (> (:cp entry) 65535) 2 1))
            result (remember-valid! (str (substring-host text 0 offset) replacement
                                        (substring-host text end (count text))))]
        (if (and (:ref? ops) ((:ref? ops) source))
          (let [node ((:node ops) world source)]
            (if (and (= 1 (:rc node)) (< (:cp entry) 128) (< cp 128))
              (do (when-not (:replace-node ops)
                    (fail "Missing unique heap String update capability" {}))
                  [((:replace-node ops) world source
                     (assoc node :text result :utf8-bytes (:bytes (encoding result)))) source])
              [((:release ops) world source 1) result]))
          [world result])))))

(defn evaluate
  "Contextual native ABI adapter. Borrow imported String/MPZ refs and raw native
   immediates without flattening the stored graph. Append/push/set consume
   their first String argument; UTF8 String getters borrow. Set preserves heap
   identity only on native unchanged/unique-ASCII paths; other results are flat
   immutable strings under the existing String carrier profile."
  [ops world symbol args]
  (if (= symbol "lean_string_utf8_set") (set-utf8 ops world args)
  (let [normalized
        (mapv (fn [i value]
                (cond
                  (or (and (zero? i) (not (contains? non-string-first-symbols symbol)))
                      (and (= 1 i) (contains? two-string-symbols symbol)))
                  (string-value ops world value)
                  (and (contains? character-symbols symbol) (= 1 i))
                  (native/unsigned-value 32 (native/number-value ops world value))
                  (= symbol "lean_uint64_mix_hash")
                  (native/unsigned-value 64 (native/number-value ops world value))
                  (or (and (= symbol "lean_string_of_usize") (zero? i))
                      (and (contains? position-symbols symbol) (= 1 i))
                      (and (= symbol "lean_string_utf8_extract") (= 2 i))
                      (and (= symbol "lean_string_memcmp") (<= 2 i 4)))
                  (try (native/nat-value ops world value)
                       (catch #?(:clj clojure.lang.ExceptionInfo :cljs :default) cause
                         (fail "Invalid or inexact string position" {:value value :cause (ex-data cause)})))
                  :else value)) (range) args)
        [after result] (evaluate-flat ops world symbol normalized)
        after (if (and (contains? #{"lean_string_append" "lean_string_push"} symbol)
                       ((:ref? ops) (first args)))
                ((:release ops) after (first args) 1) after)]
    [after result])))
