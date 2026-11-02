(ns kernel-support.scalar
  "Checked scalar storage for the explicit 64-bit little-endian guest profile.
  JVM integers cover full UInt64/USize; JS rejects values outside its exact range.
   Sparse immutable bytes preserve padding/uninitialized state and fork isolation.
   Lean float is IEEE binary64; float32 is binary32. NaNs use tagged immutable
   bytes on reads, preserving payload/signaling bits across JVM/JS snapshots.
   Use float-number explicitly for arithmetic, float-bytes for bit operations."
  (:require [kernel-support.native-scalar :as native])
  #?(:clj (:import [java.nio ByteBuffer ByteOrder])))

(defn width [type]
  (case type "uint8" 1 "uint16" 2 ("uint32" "float32") 4 ("uint64" "usize" "float") 8
        (throw (ex-info "Unsupported scalar storage type" {:type type}))))

(defn float-type? [type] (contains? #{"float" "float32"} type))

(defn integer! [type x]
  (when (float-type? type) (throw (ex-info "Expected integer scalar type" {:type type})))
  (let [n (* 8 (width type))
        ;; Native object immediates are interpreted only at this typed unbox
        ;; boundary. Raw payload bits alone cannot distinguish Nat from Int.
        x (if (native/native-scalar? x) (native/unsigned-value n x) x)]
    (when-not (and (integer? x) (<= 0 x)
                   #?(:clj (< (bigint x) (bigint (.shiftLeft java.math.BigInteger/ONE n)))
                      :cljs (and (js/Number.isSafeInteger x) (< x (js/Math.pow 2 n)))))
      (throw (ex-info "Scalar value outside supported unsigned range" {:type type :value x})))
    x))

(defn- checked-float-bytes [type bytes]
  (when-not (and (float-type? type) (vector? bytes) (= (width type) (count bytes))
                 (every? #(and (integer? %) (<= 0 % 255)) bytes))
    (throw (ex-info "Invalid IEEE scalar bytes" {:type type :bytes bytes}))) bytes)

(defn value! [type value]
  (if (float-type? type)
    (do (when-not (or (number? value)
                      (and (map? value) (= type (::type value))
                           (= #{::type ::bytes} (set (keys value)))
                           (checked-float-bytes type (::bytes value))))
          (throw (ex-info "Expected floating scalar value" {:type type :value value}))) value)
    (integer! type value)))

(defn- decode-float [type bytes]
  #?(:clj (let [buffer (doto (ByteBuffer/wrap (byte-array (map unchecked-byte bytes)))
                        (.order ByteOrder/LITTLE_ENDIAN))]
            (if (= type "float") (.getDouble buffer) (.getFloat buffer)))
     :cljs (let [buffer (js/ArrayBuffer. (width type)) view (js/DataView. buffer)]
             (doseq [i (range (width type))] (.setUint8 view i (nth bytes i)))
             (if (= type "float") (.getFloat64 view 0 true) (.getFloat32 view 0 true)))))

(defn float-number
  "Explicit numeric view. Reading a NaN may quiet/canonicalize its payload;
   use float-bytes when the exact guest IEEE representation matters."
  [type value]
  (when-not (float-type? type) (throw (ex-info "Expected floating scalar type" {:type type})))
  (value! type value)
  (if (map? value) (decode-float type (::bytes value))
    #?(:clj (if (= type "float") (.doubleValue ^Number value) (.floatValue ^Number value))
       :cljs (if (= type "float") value
               (let [view (js/DataView. (js/ArrayBuffer. 4))]
                 (.setFloat32 view 0 value true) (.getFloat32 view 0 true))))))

(defn float-bytes
  "Return exact little-endian IEEE bytes, including the original NaN payload."
  [type value]
  (value! type value)
  (when-not (float-type? type) (throw (ex-info "Expected floating scalar type" {:type type})))
  (if (map? value) (::bytes value)
    #?(:clj (let [bits (if (= type "float")
                        (Double/doubleToRawLongBits (.doubleValue ^Number value))
                        (long (Float/floatToRawIntBits (.floatValue ^Number value))))]
              (mapv #(bit-and 255 (unsigned-bit-shift-right bits (* 8 %))) (range (width type))))
       :cljs (let [view (js/DataView. (js/ArrayBuffer. (width type)))]
               (if (= type "float") (.setFloat64 view 0 value true) (.setFloat32 view 0 value true))
               (mapv #(.getUint8 view %) (range (width type)))))))

(defn float-from-bytes
  "Decode IEEE bytes. NaNs retain exact raw bytes instead of relying on host
   numeric NaN transport, which is allowed to quiet/canonicalize payloads."
  [type bytes]
  (checked-float-bytes type bytes)
  (let [number (decode-float type bytes)]
    (if #?(:clj (Double/isNaN (double number)) :cljs (js/Number.isNaN number))
      {::type type ::bytes bytes} number)))

(defn layout! [{:keys [objects usize ssize] :as layout}]
  (when-not (and (integer? objects) (<= 0 objects 1048576)
                 (integer? usize) (<= 0 usize 1048576)
                 (integer? ssize) (<= 0 ssize 1048576)
                 (< objects 256) (< (+ (* 8 usize) ssize) 1024) (pos? (+ usize ssize)))
    (throw (ex-info "Invalid scalar constructor layout" {:layout layout}))) layout)

(defn- address! [{:keys [objects usize ssize] :as layout} {:keys [index offset type region] :as slot}]
  (layout! layout)
  (when-not (and (integer? index) (<= 0 index) (integer? offset) (<= 0 offset))
    (throw (ex-info "Invalid scalar address" {:slot slot})))
  (let [address (+ (* 8 index) offset) size (width type)
        ;; Lean stores both kinds in one scalar tail. Its header does not retain
        ;; a separate usize count; uproj/sproj can view the same initialized bytes.
        lower (* 8 objects)
        upper (+ (* 8 (+ objects usize)) ssize)]
    (when-not (and (<= lower address) (<= (+ address size) upper) (zero? (mod address size))
                   (case region :usize (and (= type "usize") (zero? offset)) :scalar (not= type "usize") false))
      (throw (ex-info "Scalar access outside constructor region" {:layout layout :slot slot})))
    address))

(defn write-bytes [layout memory {:keys [type] :as slot} value]
  (let [value (value! type value)
        base (address! layout slot)]
    (if (float-type? type)
      (reduce-kv (fn [memory i byte] (assoc memory (+ base i) byte)) memory (float-bytes type value))
      (loop [i 0 value value memory memory]
        (if (= i (width type)) memory
          (recur (inc i) (quot value 256) (assoc memory (+ base i) (mod value 256))))))))

(defn read-bytes [layout memory {:keys [type] :as slot}]
  (let [base (address! layout slot)]
    (if (float-type? type)
      (float-from-bytes type (mapv (fn [i]
                                   (let [address (+ base i) byte (get memory address)]
                                     (when-not (some? byte)
                                       (throw (ex-info "Read of uninitialized scalar byte" {:address address :slot slot}))) byte))
                                 (range (width type))))
      (loop [i (dec (width type)) value 0]
        (if (neg? i) (integer! type value)
          (let [address (+ base i) byte (get memory address)]
            (when-not (some? byte) (throw (ex-info "Read of uninitialized scalar byte" {:address address :slot slot})))
            (recur (dec i) #?(:clj (+' (*' value 256) byte) :cljs (+ (* value 256) byte)))))))))

(defn box-layout [type]
  (case type
    ("uint64" "float") {:objects 0 :usize 0 :ssize 8}
    "float32" {:objects 0 :usize 0 :ssize 4}
    "usize" {:objects 0 :usize 1 :ssize 0}
    nil))

(defn box-slot [type]
  {:index 0 :offset 0 :type type :region (if (= type "usize") :usize :scalar)})

#?(:clj
   (do
     (def ^:private scalar-integer-generation (Object.))
     (def ^:private scalar-integer-roots [integer! width float-type?])
     (defn scalar-integer-token [] scalar-integer-generation)
     (defn builtin-scalar-integer? []
       (let [[i w f] scalar-integer-roots]
         (and (identical? i integer!) (identical? w width) (identical? f float-type?)
              (native/builtin-scalar-carrier?))))))
