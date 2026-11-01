(ns ansatz.lean.jvm.scalar-buffer
  "Trusted scalar/buffer codec helpers. Plans contain no guest Nodes. Borrowed
   decoders acquire/release no credits; the caller retains the actual result root."
  (:require [ansatz.lean.jvm.signature :as signature]
            [ansatz.lean.jvm.startup :as startup])
  (:import [java.math BigInteger] [java.lang.reflect Field] [java.util List]))

(def maximum-buffer-bytes 1048576)
(def maximum-array-elements 100000)
(def ^:private object-array-class (class (object-array 0)))
(def ^:private byte-array-class (class (byte-array 0)))
(def ^:private integer-classes #{Byte Short Integer Long BigInteger clojure.lang.BigInt})
(defn- need [ok code message]
  (when-not ok (throw (ex-info message {:code code}))))
(defn- cancelled! []
  (when (.isInterrupted (Thread/currentThread))
    (throw (ex-info "Scalar/buffer conversion cancelled" {:code "Cancelled"}))))
(defn- checked-type! [type]
  (signature/validate! {"arguments" [] "result" type "effect" "pure"}) type)
(defn- integer! [input]
  (need (contains? integer-classes (class input)) "UnsupportedArgumentType" "Expected an exact integer carrier")
  (let [value (cond (= BigInteger (class input)) input
                    (= clojure.lang.BigInt (class input)) (.toBigInteger ^clojure.lang.BigInt input)
                    :else (BigInteger/valueOf (.longValue ^Number input)))]
    (need (= BigInteger (class value)) "UnsupportedArgumentType" "Unsupported integer subclass")
    ;; Bound before abs/negation/range conversion allocates another large integer.
    (need (<= (.bitLength ^BigInteger value) 4096) "ResourceLimit" "Integer exceeds host codec bit budget")
    value))
(defn- width [type] (if (= "word" (get type "kind")) 64 (get type "bits")))
(defn- lane [type]
  (case (get type "kind")
    "machine-int" (str "uint" (width type))
    "word" "usize"
    "float" (if (= 32 (width type)) "float32" "float")
    "char" "uint32"
    (throw (ex-info "Not a scalar descriptor" {:code "UnsupportedSignature"}))))
(defn- scalar! [n code]
  (need (and (<= 0 n 0x10ffff) (not (<= 0xd800 n 0xdfff))) code "Char requires a Unicode scalar value") n)
(defn encode-scalar
  "Return an immediate Long or {:kind :scalar :lane String :bits Long} recipe.
   Integer inputs are range checked; signed lanes use exact two's-complement bits.
   Float32/Float require exact Float/Double carriers. Char takes a code-point integer."
  [type input]
  (checked-type! type) (cancelled!)
  (let [kind (get type "kind")]
    (case kind
      ("machine-int" "word")
      (let [bits (width type) signed (get type "signed") ^BigInteger n (integer! input)
            bound (.shiftLeft BigInteger/ONE (if signed (dec bits) bits))
            minimum (if signed (.negate bound) BigInteger/ZERO)
            maximum (.subtract bound BigInteger/ONE)]
        (need (and (not (neg? (.compareTo n minimum))) (not (pos? (.compareTo n maximum))))
              "InvalidArgument" "Integer outside the declared machine range")
        (let [mask (.subtract (.shiftLeft BigInteger/ONE bits) BigInteger/ONE)
              raw (Long/valueOf (.longValue (.and n mask)))]
          (if (< bits 64) raw {:kind :scalar :lane (lane type) :bits raw})))
      "float"
      (let [bits (width type)]
        (need (= (if (= bits 32) Float Double) (class input)) "UnsupportedArgumentType"
              "Float32/Float requires an exact Float/Double carrier")
        {:kind :scalar :lane (lane type)
         :bits (if (= bits 32)
                 (Long/valueOf (Integer/toUnsignedLong (Float/floatToRawIntBits (float input))))
                 (Long/valueOf (Double/doubleToRawLongBits (double input))))})
      "char"
      (let [^BigInteger n (integer! input)]
        (need (and (not (neg? (.signum n))) (<= (.bitLength n) 21)) "InvalidArgument" "Char code point is out of range")
        (Long/valueOf (scalar! (.longValue n) "InvalidArgument")))
      (throw (ex-info "Not a supported scalar leaf" {:code "UnsupportedArgumentType"})))))
(defn snapshot-bytes
  "Copy an exact byte[] before engine allocation; never reinterpret text as bytes."
  [input]
  (cancelled!)
  (need (= byte-array-class (class input)) "UnsupportedArgumentType" "ByteArray expects byte[]")
  (need (<= (alength ^bytes input) maximum-buffer-bytes) "ResourceLimit" "ByteArray exceeds 1 MiB host codec budget")
  (aclone ^bytes input))
(defn snapshot-array
  "Snapshot a bounded exact Object[] or indexed Java List. Recursive type checking
   and aggregate occurrence accounting remain with the caller's argument planner."
  [input]
  (cancelled!)
  (if (= object-array-class (class input))
    (do (need (<= (alength ^objects input) maximum-array-elements) "ResourceLimit" "Array exceeds host element budget")
        (vec (aclone ^objects input)))
    (do (need (and (instance? List input) (not (instance? clojure.lang.ISeq input)))
              "UnsupportedArgumentType" "Array expects Object[] or a bounded Java List")
        (let [size (.size ^List input)]
          (need (<= 0 size maximum-array-elements) "ResourceLimit" "Array exceeds host element budget")
          (let [result (loop [i 0 out (transient [])]
                         (if (= i size) (persistent! out)
                           (do (cancelled!) (recur (inc i) (conj! out (.get ^List input i))))))]
            (need (= size (.size ^List input)) "InvalidArgument" "Array extent changed during snapshot") result)))))
(defn decode-raw-scalar
  "Decode an exact scalar-lane bit word (not an object-lane scalar box).
   Machine integers/words return BigInteger, Char Integer, floats Float/Double."
  [type raw]
  (checked-type! type) (cancelled!)
  (need (= Long (class raw)) "RuntimeBoundary" "Raw scalar bits must be an exact Long")
  (let [kind (get type "kind")
        _ (need (contains? #{"machine-int" "word" "float" "char"} kind) "UnsupportedSignature" "Not a supported raw scalar")
        bits (if (= kind "char") 32 (width type)) raw (long raw)]
    (need (or (= bits 64) (and (not (neg? raw)) (< raw (bit-shift-left 1 bits))))
          "RuntimeBoundary" "Raw scalar bits exceed their declared lane")
    (case kind
      ("machine-int" "word")
      (let [unsigned (if (neg? raw) (.setBit (BigInteger/valueOf (bit-and raw Long/MAX_VALUE)) 63)
                        (BigInteger/valueOf raw))]
        (if (and (get type "signed") (.testBit unsigned (dec bits)))
          (.subtract unsigned (.shiftLeft BigInteger/ONE bits)) unsigned))
      "float" (if (= bits 32) (Float/valueOf (Float/intBitsToFloat (unchecked-int raw)))
                  (Double/valueOf (Double/longBitsToDouble raw)))
      "char" (Integer/valueOf (int (scalar! raw "RuntimeBoundary")))
      (throw (ex-info "Not a supported raw scalar" {:code "UnsupportedSignature"})))))
(defn decode-external-scalar
  "Decode takeResult's actual external scalar carrier (externalScalar in Java).
   This is distinct from guest raw IR bit words and object-lane BOX nodes."
  [type raw]
  (checked-type! type) (cancelled!)
  (if (= "float" (get type "kind"))
    (do (need (= (if (= 32 (get type "bits")) Float Double) (class raw))
              "RuntimeBoundary" "Malformed external float carrier") raw)
    (let [bits (if (= "char" (get type "kind")) 32 (width type))]
      (need (#{Long BigInteger} (class raw)) "RuntimeBoundary" "Malformed external integer carrier")
      (let [^BigInteger unsigned (if (= Long (class raw)) (BigInteger/valueOf (long raw)) raw)]
        (need (and (not (neg? (.signum unsigned))) (<= (.bitLength unsigned) bits))
              "RuntimeBoundary" "External scalar exceeds its unsigned lane")
        (decode-raw-scalar type (Long/valueOf (.longValue unsigned)))))))

(defn- cohort-class [ctx suffix]
  (let [^Class engine (:class ctx)]
    (Class/forName (str (.getName engine) "$" suffix) false (.getClassLoader engine))))
(defn- metadata [ctx raw]
  (let [sharing (cohort-class ctx "SharingMetadata")]
    (loop [value (#'startup/engine-field raw "metadata") depth 0]
      (need (< depth 128) "ResourceLimit" "Runtime metadata wrapper depth exceeds codec budget")
      (if (= sharing (class value)) (recur (#'startup/engine-field value "inner") (inc depth)) value))))
(defn- node! [ctx raw]
  (need (= (:node-class ctx) (class raw)) "RuntimeBoundary" "Expected value from the actual runtime cohort")
  (need (and (false? (#'startup/engine-field raw "dead"))
             (false? (#'startup/engine-field raw "ref"))
             (false? (#'startup/engine-field raw "readyTask"))
             (nil? (#'startup/engine-field raw "closure"))) "RuntimeBoundary" "Expected live data, not a resource/closure/task")
  (let [rc (.get ^Field (:rc ctx) raw)]
    (need (and (integer? rc) (not (neg? rc))) "RuntimeBoundary" "Invalid runtime reference count"))
  raw)
(defn- fields [ctx raw] (.get ^Field (:fields ctx) raw))
(defn- scalars [ctx raw] (.get ^Field (:scalars ctx) raw))
(defn- tag [ctx raw] (.get ^Field (:tag ctx) raw))
(defn- scalar-bits [bytes]
  (loop [i 0 bits (long 0)]
    (if (= i (alength ^bytes bytes)) bits
      (recur (inc i) (bit-or bits (bit-shift-left (long (bit-and 255 (aget ^bytes bytes i))) (* 8 i)))))))
(defn decode-scalar
  "Borrowed object-lane decoding; boxed 64-bit/Float32 payloads must match the
   reviewed BOX representation exactly. No existing Node is returned to Java."
  [ctx type raw]
  (checked-type! type) (cancelled!)
  (let [kind (get type "kind") bits (if (= kind "char") 32 (width type))
        boxed? (or (= kind "float") (= kind "word") (and (= kind "machine-int") (= bits 64)))]
    (if-not boxed? (decode-raw-scalar type raw)
      (do (node! ctx raw)
          (let [payload (scalars ctx raw) members (fields ctx raw)]
            (need (and (false? (#'startup/engine-field raw "array")) (nil? (metadata ctx raw))
                       (= 0 (tag ctx raw)) (= object-array-class (class members)) (zero? (alength ^objects members))
                       (= byte-array-class (class payload)) (= (quot bits 8) (alength ^bytes payload)))
                  "RuntimeBoundary" "Malformed runtime scalar box")
            (decode-raw-scalar type (Long/valueOf (scalar-bits payload))))))))
(defn decode-bytes
  "Copy only the live extent of an actual borrowed ByteArray."
  [ctx raw]
  (cancelled!) (node! ctx raw)
  (let [kind (metadata ctx raw) members (fields ctx raw) payload (scalars ctx raw)]
    (need (and (= (cohort-class ctx "ByteArrayState") (class kind))
               (false? (#'startup/engine-field raw "array")) (= 248 (tag ctx raw))
               (= object-array-class (class members)) (zero? (alength ^objects members))
               (= byte-array-class (class payload)) (<= (alength ^bytes payload) 16777216))
          "RuntimeBoundary" "Malformed runtime ByteArray kind/layout")
    (let [size (#'startup/engine-field kind "size")]
      (need (and (integer? size) (<= 0 size (alength ^bytes payload))) "RuntimeBoundary" "Invalid ByteArray live extent")
      (need (<= size maximum-buffer-bytes) "ResourceLimit" "ByteArray result exceeds 1 MiB host codec budget")
      (java.util.Arrays/copyOf ^bytes payload (int size)))))
(defn decode-array-fields
  "Trusted internal borrowed field snapshot, never a public decoded result.
   Caller recursively decodes every element while retaining the actual owned root."
  [ctx raw]
  (cancelled!) (node! ctx raw)
  (let [kind (metadata ctx raw) members (fields ctx raw) payload (scalars ctx raw)]
    (need (and (= (cohort-class ctx "ArrayState") (class kind))
               (true? (#'startup/engine-field raw "array")) (= 246 (tag ctx raw))
               (= object-array-class (class members)) (<= (alength ^objects members) 1000000)
               (= byte-array-class (class payload)) (zero? (alength ^bytes payload)))
          "RuntimeBoundary" "Malformed runtime Array kind/layout")
    (let [size (#'startup/engine-field kind "size")]
      (need (and (integer? size) (<= 0 size (alength ^objects members))) "RuntimeBoundary" "Invalid Array live extent")
      (need (<= size maximum-array-elements) "ResourceLimit" "Array result exceeds host element budget")
      (loop [i 0 out (transient [])]
        (if (= i size) (persistent! out)
          (do (cancelled!)
              (need (some? (aget ^objects members i)) "RuntimeBoundary" "Array live field is null")
              (recur (inc i) (conj! out (aget ^objects members i)))))))))
