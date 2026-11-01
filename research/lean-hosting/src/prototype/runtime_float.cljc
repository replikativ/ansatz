(ns prototype.runtime-float
  "Lean Float/Float32 bitcasts for the pinned little-endian profile.
   Public Lean bitcasts canonicalize NaNs; raw scalar storage preserves payloads.
   UInt64 uses exact JVM integers; JS rejects unsafe integer carriers explicitly."
  (:require [prototype.scalar :as scalar]
            [prototype.native-scalar :as native]))

(def arithmetic-symbols
  (into {} (for [[prefix float-type] [["lean_float_" "float"] ["lean_float32_" "float32"]]
                 [suffix operation arity] [["add" :add 2] ["sub" :sub 2] ["mul" :mul 2] ["div" :div 2]
                                           ["negate" :negate 1] ["beq" :eq 2] ["decLe" :le 2] ["decLt" :lt 2]]]
             [(str prefix suffix) {:arity arity :operation operation :float-type float-type}])))

(def supported-symbols
  (merge arithmetic-symbols {"lean_float_of_bits" {:arity 1}
   "lean_float_to_bits" {:arity 1}
   "lean_float32_of_bits" {:arity 1}
   "lean_float32_to_bits" {:arity 1}
   "lean_uint32_to_float" {:arity 1}
   "lean_uint64_to_float" {:arity 1}
   "lean_uint32_to_float32" {:arity 1}
   "lean_uint64_to_float32" {:arity 1}
   "lean_mk_empty_float_array" {:arity 1}}))

(defn- fail [message data] (throw (ex-info message data)))

(defn- canonical-float [float-type value]
  ;; Pinned runtime/object.cpp explicitly replaces every NaN in both public
  ;; bitcast directions with numeric_limits<T>::quiet_NaN(). On this x86-64
  ;; profile that is positive qNaN, with no payload. Storage has a separate ABI.
  (let [number (scalar/float-number float-type value)]
    (if #?(:clj (Double/isNaN (double number)) :cljs (js/Number.isNaN number))
      (scalar/float-from-bytes float-type
        (if (= float-type "float") [0 0 0 0 0 0 248 127] [0 0 192 127]))
      value)))

(defn- of-bits [float-type integer-type bits]
  (let [bits (scalar/integer! integer-type bits)
        layout {:objects 0 :usize 0 :ssize (scalar/width integer-type)}
        slot {:index 0 :offset 0 :type integer-type :region :scalar}
        memory (scalar/write-bytes layout {} slot bits)]
    (canonical-float float-type
      (scalar/float-from-bytes float-type (mapv memory (range (scalar/width integer-type)))))))

(defn- to-bits [float-type integer-type value]
  (let [bytes (scalar/float-bytes float-type (canonical-float float-type value))
        layout {:objects 0 :usize 0 :ssize (count bytes)}
        slot {:index 0 :offset 0 :type integer-type :region :scalar}]
    (scalar/read-bytes layout (zipmap (range (count bytes)) bytes) slot)))

(defn- unsigned-to-float [float-type integer-type value]
  (let [value (scalar/integer! integer-type value)]
    ;; BigInteger.floatValue rounds directly to binary32; converting via double
    ;; can double-round UInt64 values near a binary32 halfway point.
    #?(:clj (if (= float-type "float") (.doubleValue ^Number value) (.floatValue ^Number value))
       :cljs (scalar/float-number float-type value))))

(defn- nan? [number]
  #?(:clj (Double/isNaN (double number)) :cljs (js/Number.isNaN number)))

(defn- quiet-nan [float-type value]
  (let [bytes (scalar/float-bytes float-type value)
        index (if (= float-type "float") 6 2)
        mask (if (= float-type "float") 8 64)]
    (scalar/float-from-bytes float-type (update bytes index bit-or mask))))

(defn- arithmetic [float-type operation args]
  (let [left (first args) right (second args)
        a (scalar/float-number float-type left)]
    (if (= :negate operation)
      ;; C unary negation toggles the sign bit, including signaling NaNs.
      (let [bytes (scalar/float-bytes float-type left)]
        (scalar/float-from-bytes float-type (update bytes (dec (count bytes)) bit-xor 128)))
      (let [b (scalar/float-number float-type right)]
        (case operation
          :eq (if #?(:clj (== (double a) (double b)) :cljs (== a b)) 1 0)
          :le (if (<= a b) 1 0)
          :lt (if (< a b) 1 0)
          ;; Pinned x86-64 native oracle: first NaN operand wins and is
          ;; quieted. Invalid operations without NaN inputs produce -qNaN.
          ;; Explicit bytes avoid JVM/JS losing payloads or changing signs.
          (cond
            (nan? a) (quiet-nan float-type left)
            (nan? b) (quiet-nan float-type right)
            :else
            (let [result #?(:clj (case operation
                                  :add (+ (double a) (double b))
                                  :sub (- (double a) (double b))
                                  :mul (* (double a) (double b))
                                  :div (/ (double a) (double b)))
                            :cljs (case operation :add (+ a b) :sub (- a b) :mul (* a b) :div (/ a b)))]
              (if (nan? result)
                (scalar/float-from-bytes float-type
                  (if (= float-type "float") [0 0 0 0 0 0 248 255] [0 0 192 255]))
                ;; binary32 inputs are exact doubles; add/sub/mul/div then
                ;; round once to binary32. For division, a 24-bit denominator
                ;; cannot get close enough to a binary32 midpoint to double-round.
                (scalar/float-number float-type result)))))))))

(defn evaluate
  "Raw floating ABI. Arithmetic preserves signed zeros, quiets input NaNs and
   rounds to binary64/binary32; comparisons return UInt8 and leave NaNs unordered.
   Public bitcasts canonicalize NaNs; raw storage/negation retain their bits.
   Unsigned numeric conversions round directly to the target IEEE width."
  [ops world symbol args]
  (let [spec (get supported-symbols symbol)]
    (when-not spec (fail "Unsupported floating runtime extern" {:symbol symbol}))
    (when-not (= (:arity spec) (count args))
      (fail "Floating runtime arity mismatch" {:symbol symbol :arity (count args)})))
  (let [value (first args)]
    (cond
      (contains? arithmetic-symbols symbol)
      (let [{:keys [float-type operation]} (get arithmetic-symbols symbol)]
        [world (arithmetic float-type operation args)])
      (= symbol "lean_mk_empty_float_array")
      (let [value (native/nat-value value)]
        ;; Native lean_mk_empty_float_array requires an immediate/small Nat.
        (when (> value #?(:clj 9223372036854775807 :cljs js/Number.MAX_SAFE_INTEGER))
          (fail "FloatArray capacity exceeds tagged Nat profile" {:capacity value}))
        (let [[world result] ((:allocate ops) world :float-array 248 [])
              node ((:node ops) world result)]
          [((:replace-node ops) world result (assoc node :values [])) result]))
      :else [world (case symbol
             "lean_float_of_bits" (of-bits "float" "uint64" value)
             "lean_float_to_bits" (to-bits "float" "uint64" value)
             "lean_float32_of_bits" (of-bits "float32" "uint32" value)
             "lean_float32_to_bits" (to-bits "float32" "uint32" value)
             "lean_uint32_to_float" (unsigned-to-float "float" "uint32" value)
             "lean_uint64_to_float" (unsigned-to-float "float" "uint64" value)
             "lean_uint32_to_float32" (unsigned-to-float "float32" "uint32" value)
             "lean_uint64_to_float32" (unsigned-to-float "float32" "uint64" value))])))
