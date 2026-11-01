(ns prototype.checkpoint-wire
  "Draft bounded row framing. No handlers, generic Java serialization or read-eval."
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [prototype.machine :as m]
            [prototype.native-scalar :as native])
  (:import [java.io DataInputStream DataOutputStream PushbackReader StringReader EOFException
            OutputStream OutputStreamWriter Writer InputStream]
           [java.nio ByteBuffer]
           [java.nio.charset StandardCharsets CodingErrorAction]
           [java.security MessageDigest]))

(def max-row-bytes (* 64 1024 1024))
(defn fail [message data] (throw (ex-info message data)))
(defn check [ok message] (when-not ok (fail message {})))
(defn sha256 [bytes]
  (.formatHex (java.util.HexFormat/of) (.digest (MessageDigest/getInstance "SHA-256") ^bytes bytes)))
(defn file-sha256 [path]
  (with-open [input (io/input-stream path)]
    (let [md (MessageDigest/getInstance "SHA-256") bytes (byte-array 65536)]
      (loop [] (let [n (.read input bytes)] (when (pos? n) (.update md bytes 0 n) (recur))))
      (.formatHex (java.util.HexFormat/of) (.digest md)))))
(defn hash? [x] (and (string? x) (boolean (re-matches #"[0-9a-f]{64}" x))))
(defn worker [f]
  ;; Same bounded worker-stack approach as bootstrap-archive; no guest thread.
  (let [result (promise)
        thread (Thread. nil (reify Runnable
                              (run [_] (try (deliver result [:ok (f)])
                                            (catch Throwable e (deliver result [:error e])))))
                        "ansatz-finalizer-checkpoint" (* 16 1024 1024))]
    (.start thread)
    (let [[kind value] @result] (if (= :ok kind) value (throw value)))))

(defn- fixed-record [kind constructor keys]
  (fn [value]
    (check (and (map? value) (= keys (set (clojure.core/keys value)))) (str "Malformed checkpoint " kind))
    (constructor value)))
(def readers
  {'prototype.machine.Ref (fixed-record :ref m/map->Ref #{:id})
   'prototype.machine.Tag (fixed-record :tag m/map->Tag #{:tag})
   'prototype.machine.Builtin (fixed-record :builtin m/map->Builtin #{:name})
   'prototype.native_scalar.RawNativeScalar
   (fixed-record :native-scalar #(native/native-scalar (:payload %)) #{:payload})
   'ansatz.checkpoint/float32
   (fn [text]
     (check (and (string? text) (re-matches #"[0-9a-f]{8}" text)) "Malformed Float bits")
     (Float/intBitsToFloat (Integer/parseUnsignedInt text 16)))
   'ansatz.checkpoint/float64
   (fn [text]
     (check (and (string? text) (re-matches #"[0-9a-f]{16}" text)) "Malformed Double bits")
     (Double/longBitsToDouble (Long/parseUnsignedLong text 16)))
   'inst (fn [_] (fail "Unsupported checkpoint tag" {:tag 'inst}))
   'uuid (fn [_] (fail "Unsupported checkpoint tag" {:tag 'uuid}))})

(defn- visit-wire-value [root emit?]
  ;; One acceptance policy for transformation and validation. Validation visits
  ;; every same child/metadata edge. Exact standard sequences avoid discarded
  ;; AST containers; custom sequences retain the complete transforming path.
  ;; Float keys/set members are explicitly unsupported (NaN key equality).
  (letfn [(visit [x keyed? emit?]
            (if (and (not emit?) (or (vector? x) (list? x))
                     (not (or (identical? clojure.lang.PersistentVector (class x))
                              (identical? clojure.lang.PersistentList (class x))
                              (identical? (class '()) (class x)))))
              ;; A custom reduction can inspect the initial accumulator or the
              ;; reducer result. Preserve its complete old transforming path,
              ;; including the incoming key context and one metadata traversal.
              (visit x keyed? true)
              (do
                (when (and keyed? (or (instance? Float x) (instance? Double x)))
                  (fail "Float inside a map key or set member is outside v1" {}))
                (let [result
                      (cond
                        (instance? Float x) (if emit? (tagged-literal 'ansatz.checkpoint/float32 (format "%08x" (Float/floatToRawIntBits x))) x)
                        (instance? Double x) (if emit? (tagged-literal 'ansatz.checkpoint/float64 (format "%016x" (Double/doubleToRawLongBits x))) x)
                        (or (m/ref? x) (instance? prototype.machine.Tag x)
                            (instance? prototype.machine.Builtin x) (native/native-scalar? x))
                        (do
                          (check (nil? (meta x)) "Metadata on guest carrier is outside v1")
                          (cond
                            (m/ref? x) (check (and (= #{:id} (set (keys x))) (integer? (:id x)) (<= 0 (:id x) Long/MAX_VALUE)) "Invalid guest Ref")
                            (instance? prototype.machine.Tag x) (check (and (= #{:tag} (set (keys x))) (integer? (:tag x)) (<= 0 (:tag x) 255)) "Invalid guest Tag")
                            (instance? prototype.machine.Builtin x) (check (and (= #{:name} (set (keys x))) (= :inc (:name x))) "Unsupported guest Builtin")
                            :else (do (check (= #{:payload} (set (keys x))) "Invalid native scalar fields") (native/native-scalar (:payload x))))
                          x)
                        (record? x) (fail "Unsupported checkpoint record" {:class (.getName (class x))})
                        (map? x)
                        (do
                          (check (contains? #{"clojure.lang.PersistentArrayMap" "clojure.lang.PersistentHashMap"}
                                            (.getName (class x))) "Unsupported map implementation")
                          (if emit?
                            (reduce-kv (fn [out k v]
                                         (check (not (or (instance? Float k) (instance? Double k))) "Float map keys are outside v1")
                                         (assoc out (visit k true emit?) (visit v keyed? emit?))) (empty x) x)
                            (do (reduce-kv (fn [_ k v]
                                             (check (not (or (instance? Float k) (instance? Double k))) "Float map keys are outside v1")
                                             (visit k true emit?) (visit v keyed? emit?) nil) nil x) x)))
                        (vector? x) (if emit? (with-meta (mapv #(visit % keyed? emit?) x) (meta x))
                                        (do (reduce (fn [_ v] (visit v keyed? emit?) nil) nil x) x))
                        (list? x) (if emit? (with-meta (apply list (mapv #(visit % keyed? emit?) x)) (meta x))
                                      (do (reduce (fn [_ v] (visit v keyed? emit?) nil) nil x) x))
                        (set? x) (do
                                   (check (= "clojure.lang.PersistentHashSet" (.getName (class x))) "Unsupported set implementation")
                                   (doseq [v x] (check (not (or (instance? Float v) (instance? Double v))) "Float set members are outside v1"))
                                   (if emit? (into #{} (map #(visit % true emit?)) x)
                                       (do (doseq [v x] (visit v true emit?)) x)))
                        (or (nil? x) (string? x) (boolean? x) (char? x) (symbol? x) (keyword? x)
                            (integer? x) (instance? java.math.BigDecimal x) (ratio? x)) x
                        :else (fail "Opaque checkpoint value" {:class (.getName (class x))}))]
                  (if-let [metadata (meta x)]
                    (do
                      (check (instance? clojure.lang.IObj result) "Metadata on unsupported scalar")
                      (let [next-metadata (visit metadata keyed? emit?)]
                        (if emit? (with-meta result next-metadata) result))) result)))))]
    (visit root false emit?)))

(defn wire-value [root]
  ;; Transform ONE bounded row; never make a transformed whole-world copy.
  (visit-wire-value root true))

(defn validate-value!
  "Apply wire-value's complete acceptance policy. Exact standard collections
   avoid reconstruction; custom sequence classes keep the transforming fallback.
   Returns the identical input. This grants no kernel or executable authority."
  [root]
  (visit-wire-value root false)
  root)

(defn- bounded-sink [limit]
  (check (and (integer? limit) (<= 0 limit Integer/MAX_VALUE)) "Invalid bounded byte limit")
  ;; Chunk capacities sum to at most LIMIT. No oversized byte array or doubled
  ;; ByteArrayOutputStream backing array is allocated before rejecting a write.
  (let [state (atom {:chunks [] :current nil :used 0 :total 0})
        append! (fn [^bytes bytes offset length]
                  (check (and (integer? offset) (integer? length)
                              (<= 0 offset) (<= 0 length) (<= (+ offset length) (alength bytes)))
                         "Invalid bounded write")
                  (check (<= (+ (:total @state) length) limit) "Checkpoint byte size exceeds limit")
                  (loop [s @state offset offset left length]
                    (if (zero? left) (reset! state s)
                      (let [buffer (or (:current s) (byte-array (min 8192 (- limit (:total s)))))
                            n (min left (- (alength ^bytes buffer) (:used s)))
                            used (+ (:used s) n)
                            next (assoc s :current buffer :used used :total (+ (:total s) n))]
                        (System/arraycopy bytes offset buffer (:used s) n)
                        (recur (if (= used (alength ^bytes buffer))
                                 (assoc next :chunks (conj (:chunks next) buffer) :current nil :used 0)
                                 next)
                               (+ offset n) (- left n))))))
        stream (proxy [OutputStream] []
                 (write
                   ([value]
                    (if (instance? (Class/forName "[B") value)
                      (append! value 0 (alength ^bytes value))
                      (append! (byte-array [(unchecked-byte value)]) 0 1)))
                   ([bytes offset length] (append! bytes offset length))))]
    {:stream stream
     :bytes (fn []
              (let [{:keys [chunks current used total]} @state result (byte-array total)]
                (loop [chunks (seq chunks) offset 0]
                  (if-let [chunk (first chunks)]
                    (do (System/arraycopy chunk 0 result offset (alength ^bytes chunk))
                        (recur (next chunks) (+ offset (alength ^bytes chunk))))
                    (when current (System/arraycopy current 0 result offset used))))
                result))}))

(defn read-bounded-bytes
  "Read at most LIMIT bytes through ONE already-open stream. Probe at most one
   extra byte to detect growth; never use available/length as allocation proof.
   Does not close the caller's stream. The returned bytes are exactly what was
   consumed and can be hashed+decoded without reopening an attacker-owned path."
  [^InputStream input limit]
  (let [{:keys [stream bytes]} (bounded-sink limit) buffer (byte-array 8192)]
    (loop [total 0]
      (let [requested (min 8192 (inc (- limit total)))
            n (.read input buffer 0 (int requested))]
        (cond
          (= -1 n) (bytes)
          (zero? n) (fail "Bounded input stream made no progress" {})
          :else (do (check (<= 1 n requested) "Invalid bounded input read")
                    (.write ^OutputStream stream buffer 0 n)
                    (recur (+ total n))))))))

(defn read-file-bytes
  "One-open bounded file read; callers hash and decode these SAME bytes. No
   size-check/reopen race, and growth beyond LIMIT is rejected while reading."
  [path limit]
  (with-open [input (io/input-stream path)] (read-bounded-bytes input limit)))

(defn utf8-string [bytes]
  (let [decoder (doto (.newDecoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT)
                  (.onUnmappableCharacter CodingErrorAction/REPORT))]
    (str (.decode decoder (ByteBuffer/wrap bytes)))))

(defn- integer-size! [n]
  ;; Before Java decimal conversion can allocate, bound its decimal digit count
  ;; from bitLength. The conservative lower bound can differ by one digit; it
  ;; cannot permit an arbitrarily large scalar before the streaming cap acts.
  (let [n (cond (instance? java.math.BigInteger n) n
                (instance? clojure.lang.BigInt n) (.toBigInteger ^clojure.lang.BigInt n)
                :else nil)]
    (when n
      (check (<= (long (Math/floor (* (max 0 (dec (.bitLength ^java.math.BigInteger n)))
                                     0.3010299956639812))) max-row-bytes)
             "Checkpoint numeric scalar exceeds limit"))))

(defn- write-value! [^Writer writer root]
  ;; Stream directly from the immutable row: no transformed row or full pr-str
  ;; intermediate. Literal string escapes are emitted incrementally as well.
  (letfn [(text! [^String text]
            ;; Some JDK Writer String paths copy the entire requested slice to
            ;; char[]. Slice explicitly so a huge existing symbol/string cannot
            ;; allocate an unbounded UTF-16 temporary before the byte cap acts.
            (loop [offset 0]
              (when (< offset (.length text))
                (let [n (min 2048 (- (.length text) offset))]
                  (.write writer text offset n)
                  (recur (+ offset n))))))
          (string! [^String text]
            (text! "\"")
            (dotimes [i (.length text)]
              (let [c (.charAt text i)]
                (case c
                  \" (text! "\\\"")
                  \\ (text! "\\\\")
                  \newline (text! "\\n")
                  \return (text! "\\r")
                  \tab (text! "\\t")
                  \backspace (text! "\\b")
                  \formfeed (text! "\\f")
                  (if (< (int c) 32) (text! (format "\\u%04x" (int c)))
                      (.write writer (int c))))))
            (text! "\""))
          (items! [start end items keyed?]
            (text! start)
            (loop [items (seq items) first? true]
              (when (seq items)
                (when-not first? (text! " ")) (visit (first items) keyed?)
                (recur (next items) false)))
            (text! end))
          (visit [x keyed?]
            (when (and keyed? (or (instance? Float x) (instance? Double x)))
              (fail "Float inside a map key or set member is outside v1" {}))
            (when-let [metadata (meta x)]
              (check (instance? clojure.lang.IObj x) "Metadata on unsupported scalar")
              (check (not (or (m/ref? x) (instance? prototype.machine.Tag x)
                              (instance? prototype.machine.Builtin x) (native/native-scalar? x)))
                     "Metadata on guest carrier is outside v1")
              (text! "^") (visit metadata keyed?) (text! " "))
            (cond
              (instance? Float x)
              (do (text! "#ansatz.checkpoint/float32 ") (string! (format "%08x" (Float/floatToRawIntBits x))))
              (instance? Double x)
              (do (text! "#ansatz.checkpoint/float64 ") (string! (format "%016x" (Double/doubleToRawLongBits x))))
              (or (m/ref? x) (instance? prototype.machine.Tag x)
                  (instance? prototype.machine.Builtin x) (native/native-scalar? x))
              (do (wire-value x)
                  (cond
                    (m/ref? x) (do (text! "#prototype.machine.Ref ") (visit {:id (:id x)} keyed?))
                    (instance? prototype.machine.Tag x) (do (text! "#prototype.machine.Tag ") (visit {:tag (:tag x)} keyed?))
                    (instance? prototype.machine.Builtin x) (do (text! "#prototype.machine.Builtin ") (visit {:name (:name x)} keyed?))
                    :else (do (text! "#prototype.native_scalar.RawNativeScalar ") (visit {:payload (:payload x)} keyed?))))
              (record? x) (fail "Unsupported checkpoint record" {:class (.getName (class x))})
              (map? x)
              (do (check (contains? #{"clojure.lang.PersistentArrayMap" "clojure.lang.PersistentHashMap"}
                                     (.getName (class x))) "Unsupported map implementation")
                  (text! "{")
                  (loop [entries (seq x) first? true]
                    (when-let [entry (first entries)]
                      (when-not first? (text! " "))
                      (visit (key entry) true) (text! " ") (visit (val entry) keyed?)
                      (recur (next entries) false)))
                  (text! "}"))
              (vector? x) (items! "[" "]" x keyed?)
              (list? x) (items! "(" ")" x keyed?)
              (set? x) (do (check (= "clojure.lang.PersistentHashSet" (.getName (class x))) "Unsupported set implementation")
                           (items! "#{" "}" x true))
              (string? x) (string! x)
              (nil? x) (text! "nil")
              (boolean? x) (text! (if x "true" "false"))
              (or (keyword? x) (symbol? x))
              (do (when (keyword? x) (text! ":"))
                  (when-let [namespace (namespace x)] (text! namespace) (text! "/"))
                  (text! (name x)))
              (integer? x) (do (integer-size! x) (text! (str x))
                               (when (instance? clojure.lang.BigInt x) (text! "N")))
              (instance? java.math.BigDecimal x)
              (do (integer-size! (.unscaledValue ^java.math.BigDecimal x)) (text! (.toString ^java.math.BigDecimal x)) (text! "M"))
              (ratio? x) (do (integer-size! (numerator x)) (integer-size! (denominator x))
                             (text! (str (numerator x))) (text! "/") (text! (str (denominator x))))
              (char? x) (binding [*out* writer *print-readably* true *print-dup* false] (pr x))
              :else (fail "Opaque checkpoint value" {:class (.getName (class x))})))]
    (visit root false)))

(defn encode [row]
  (let [{:keys [stream bytes]} (bounded-sink max-row-bytes)
        encoder (doto (.newEncoder StandardCharsets/UTF_8)
                  (.onMalformedInput CodingErrorAction/REPORT)
                  (.onUnmappableCharacter CodingErrorAction/REPORT))
        writer (OutputStreamWriter. ^OutputStream stream ^java.nio.charset.CharsetEncoder encoder)]
    (write-value! writer row)
    ;; close, not only flush, validates a trailing unpaired UTF-16 surrogate.
    ;; All storage is private memory; an encoding exception has no file owner.
    (.close writer)
    (bytes)))
(defn decode [bytes]
  (let [text (utf8-string bytes) eof (Object.)]
    (with-open [reader (PushbackReader. (StringReader. text))]
      (let [options {:eof eof :readers readers :default (fn [tag _] (fail "Unknown checkpoint tag" {:tag tag}))}
            row (edn/read options reader)]
        (check (not (identical? eof row)) "Empty checkpoint frame")
        (check (identical? eof (edn/read options reader)) "Multiple values in checkpoint frame")
        ;; Also rejects unknown records/classes produced by custom readers.
        (validate-value! row)
        row))))
(defn write-frame! [^DataOutputStream output row]
  (let [bytes (encode row)]
    (check (<= 1 (alength bytes) max-row-bytes) "Checkpoint row size exceeds limit")
    (.writeInt output (alength bytes)) (.write output bytes)))
(defn read-frame! [^DataInputStream input]
  ;; A clean end is explicit :end, so ALL premature EOFs are errors.
  (let [length (.readInt input)]
    (check (<= 1 length max-row-bytes) "Invalid checkpoint frame length")
    (let [bytes (byte-array length)] (.readFully input bytes) (decode bytes))))
(defn same-data? [left right]
  ;; Bootstrap's iterative metadata-aware row comparison, extended by encoding
  ;; floats to exact raw bits first. Map iteration order does not affect equality.
  (loop [pending [[(wire-value left) (wire-value right) false]]]
    (if (empty? pending) true
      (let [[a b meta?] (peek pending) pending (pop pending)]
        (cond
          (and (not meta?) (not (identical? (meta a) (meta b))))
          (recur (conj pending [a b true] [(meta a) (meta b) false]))
          (identical? a b) (recur pending)
          (map? a)
          (if (and (map? b) (= (count a) (count b)) (= (record? a) (record? b))
                   (or (not (record? a)) (= (class a) (class b))))
            (let [pairs (map (fn [[k v]] (when-let [entry (find b k)] [[k (key entry) false] [v (val entry) false]])) a)]
              (if (every? some? pairs) (recur (into pending (mapcat identity pairs))) false)) false)
          (or (vector? a) (list? a))
          (if (and (if (vector? a) (vector? b) (list? b)) (= (count a) (count b)))
            (recur (into pending (map #(vector %1 %2 false) a b))) false)
          (set? a) (if (and (set? b) (= (count a) (count b)) (every? #(contains? b %) a))
                     (recur (into pending (map #(vector % (get b %) false) a))) false)
          (or (map? b) (vector? b) (list? b) (set? b)) false
          (= a b) (recur pending)
          :else false)))))

(defn share-name-prefixes
  "Share exact metadata-free Name trees within one restore. The map contains
   ONLY canonical Name vectors, never functions, arbitrary vectors or records."
  [^java.util.HashMap names root]
  (letfn [(visit [value]
            (let [changed
                  (cond
                    (vector? value)
                    (reduce-kv (fn [out index child]
                                 (let [next-child (visit child)]
                                   (if (identical? child next-child) out (assoc out index next-child))))
                               value value)
                    (map? value)
                    ;; Starting from the original also preserves Ref/Tag/Builtin
                    ;; record types. Fixed record keys are unchanged keywords.
                    (reduce-kv (fn [out key child]
                                 (let [next-key (visit key) next-child (visit child)]
                                   (cond
                                     (and (identical? key next-key) (identical? child next-child)) out
                                     (identical? key next-key) (assoc out key next-child)
                                     :else (assoc (dissoc out key) next-key next-child))))
                               value value)
                    (list? value)
                    (let [children (mapv visit value)]
                      (if (every? true? (map identical? value children)) value
                          (with-meta (apply list children) (meta value))))
                    (set? value)
                    (reduce (fn [out child]
                              (let [next-child (visit child)]
                                (if (identical? child next-child) out
                                    (conj (disj out child) next-child)))) value value)
                    :else value)
                  metadata (meta value)
                  next-metadata (when metadata (visit metadata))
                  changed (if (identical? metadata next-metadata) changed
                              (with-meta changed next-metadata))]
              (if (and (vector? changed) (nil? (meta changed))
                       (or (and (= 1 (count changed)) (= "anonymous" (first changed)))
                           (and (= 3 (count changed))
                                (let [[kind prefix component] changed]
                                  (and (string? component)
                                       (or (= "str" kind)
                                           (and (= "num" kind) (re-matches #"[0-9]+" component)))
                                       (vector? prefix)
                                       ;; Equality ignores metadata. Identity with
                                       ;; a previously canonical prefix proves the
                                       ;; ENTIRE prefix chain was metadata-free.
                                       (identical? prefix (.get names prefix)))))))
                (or (.get names changed)
                    (do (.put names changed changed) changed))
                changed)))]
    (visit root)))

