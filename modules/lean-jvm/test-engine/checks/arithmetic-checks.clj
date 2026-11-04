(ns java-ir-arithmetic-checks
  "Integer arithmetic completion: Int multiplication/division, Nat bitwise/gcd/pred and
   the fixed-width unsigned matrix, against an independent BigInteger model."
  (:require [clojure.test :refer [deftest is run-tests]]
            [java-ir-baseline :as j] [java-ir-baseline-checks :as c]
            [java-ir-extern-checks :as x]))
(def ^:dynamic *basis* nil)

;; [declaration symbol param-types borrowed result], verbatim from Lean.IR.findEnvDecl
;; over Init/Std in Lean 4.33.1 (819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
(def abis
  [
   ["Bool.toUInt16" "lean_bool_to_uint16" ["uint8"] [false] "uint16"]
   ["Bool.toUInt32" "lean_bool_to_uint32" ["uint8"] [false] "uint32"]
   ["Bool.toUInt8" "lean_bool_to_uint8" ["uint8"] [false] "uint8"]
   ["Bool.toUSize" "lean_bool_to_usize" ["uint8"] [false] "usize"]
   ["Int.decNonneg" "lean_int_dec_nonneg" ["tobject"] [true] "uint8"]
   ["Int.divExact" "lean_int_div_exact" ["tobject" "tobject" "erased"] [true true false] "tobject"]
   ["Int.tdiv" "lean_int_div" ["tobject" "tobject"] [true true] "tobject"]
   ["Int.ediv" "lean_int_ediv" ["tobject" "tobject"] [true true] "tobject"]
   ["Int.emod" "lean_int_emod" ["tobject" "tobject"] [true true] "tobject"]
   ["Int.tmod" "lean_int_mod" ["tobject" "tobject"] [true true] "tobject"]
   ["Int.mul" "lean_int_mul" ["tobject" "tobject"] [true true] "tobject"]
   ["Nat.divExact" "lean_nat_div_exact" ["tobject" "tobject" "erased"] [true true false] "tobject"]
   ["Nat.gcd" "lean_nat_gcd" ["tobject" "tobject"] [true true] "tobject"]
   ["Nat.land" "lean_nat_land" ["tobject" "tobject"] [true true] "tobject"]
   ["Nat.xor" "lean_nat_lxor" ["tobject" "tobject"] [true true] "tobject"]
   ["Nat.pred" "lean_nat_pred" ["tobject"] [true] "tobject"]
   ["UInt16.add" "lean_uint16_add" ["uint16" "uint16"] [false false] "uint16"]
   ["UInt16.complement" "lean_uint16_complement" ["uint16"] [false] "uint16"]
   ["UInt16.decLe" "lean_uint16_dec_le" ["uint16" "uint16"] [false false] "uint8"]
   ["UInt16.decLt" "lean_uint16_dec_lt" ["uint16" "uint16"] [false false] "uint8"]
   ["UInt16.div" "lean_uint16_div" ["uint16" "uint16"] [false false] "uint16"]
   ["UInt16.land" "lean_uint16_land" ["uint16" "uint16"] [false false] "uint16"]
   ["UInt16.log2" "lean_uint16_log2" ["uint16"] [false] "uint16"]
   ["UInt16.lor" "lean_uint16_lor" ["uint16" "uint16"] [false false] "uint16"]
   ["UInt16.mod" "lean_uint16_mod" ["uint16" "uint16"] [false false] "uint16"]
   ["UInt16.mul" "lean_uint16_mul" ["uint16" "uint16"] [false false] "uint16"]
   ["UInt16.neg" "lean_uint16_neg" ["uint16"] [false] "uint16"]
   ["UInt16.shiftLeft" "lean_uint16_shift_left" ["uint16" "uint16"] [false false] "uint16"]
   ["UInt16.shiftRight" "lean_uint16_shift_right" ["uint16" "uint16"] [false false] "uint16"]
   ["UInt16.sub" "lean_uint16_sub" ["uint16" "uint16"] [false false] "uint16"]
   ["UInt16.toFloat32" "lean_uint16_to_float32" ["uint16"] [false] "float32"]
   ["UInt16.toFloat" "lean_uint16_to_float" ["uint16"] [false] "float"]
   ["UInt16.toBitVec" "lean_uint16_to_nat" ["uint16"] [false] "tobject"]
   ["UInt16.toUInt32" "lean_uint16_to_uint32" ["uint16"] [false] "uint32"]
   ["UInt16.toUInt64" "lean_uint16_to_uint64" ["uint16"] [false] "uint64"]
   ["UInt16.toUInt8" "lean_uint16_to_uint8" ["uint16"] [false] "uint8"]
   ["UInt16.toUSize" "lean_uint16_to_usize" ["uint16"] [false] "usize"]
   ["UInt16.xor" "lean_uint16_xor" ["uint16" "uint16"] [false false] "uint16"]
   ["UInt32.complement" "lean_uint32_complement" ["uint32"] [false] "uint32"]
   ["UInt32.div" "lean_uint32_div" ["uint32" "uint32"] [false false] "uint32"]
   ["UInt32.land" "lean_uint32_land" ["uint32" "uint32"] [false false] "uint32"]
   ["UInt32.log2" "lean_uint32_log2" ["uint32"] [false] "uint32"]
   ["UInt32.lor" "lean_uint32_lor" ["uint32" "uint32"] [false false] "uint32"]
   ["UInt32.mod" "lean_uint32_mod" ["uint32" "uint32"] [false false] "uint32"]
   ["UInt32.mul" "lean_uint32_mul" ["uint32" "uint32"] [false false] "uint32"]
   ["UInt32.neg" "lean_uint32_neg" ["uint32"] [false] "uint32"]
   ["UInt32.shiftLeft" "lean_uint32_shift_left" ["uint32" "uint32"] [false false] "uint32"]
   ["UInt32.shiftRight" "lean_uint32_shift_right" ["uint32" "uint32"] [false false] "uint32"]
   ["UInt32.sub" "lean_uint32_sub" ["uint32" "uint32"] [false false] "uint32"]
   ["UInt32.toFloat32" "lean_uint32_to_float32" ["uint32"] [false] "float32"]
   ["UInt32.toFloat" "lean_uint32_to_float" ["uint32"] [false] "float"]
   ["UInt32.toUInt16" "lean_uint32_to_uint16" ["uint32"] [false] "uint16"]
   ["UInt32.toUSize" "lean_uint32_to_usize" ["uint32"] [false] "usize"]
   ["UInt32.xor" "lean_uint32_xor" ["uint32" "uint32"] [false false] "uint32"]
   ["UInt64.toUInt16" "lean_uint64_to_uint16" ["uint64"] [false] "uint16"]
   ["UInt8.complement" "lean_uint8_complement" ["uint8"] [false] "uint8"]
   ["UInt8.decLt" "lean_uint8_dec_lt" ["uint8" "uint8"] [false false] "uint8"]
   ["UInt8.div" "lean_uint8_div" ["uint8" "uint8"] [false false] "uint8"]
   ["UInt8.log2" "lean_uint8_log2" ["uint8"] [false] "uint8"]
   ["UInt8.lor" "lean_uint8_lor" ["uint8" "uint8"] [false false] "uint8"]
   ["UInt8.mod" "lean_uint8_mod" ["uint8" "uint8"] [false false] "uint8"]
   ["UInt8.mul" "lean_uint8_mul" ["uint8" "uint8"] [false false] "uint8"]
   ["UInt8.neg" "lean_uint8_neg" ["uint8"] [false] "uint8"]
   ["UInt8.shiftLeft" "lean_uint8_shift_left" ["uint8" "uint8"] [false false] "uint8"]
   ["UInt8.shiftRight" "lean_uint8_shift_right" ["uint8" "uint8"] [false false] "uint8"]
   ["UInt8.sub" "lean_uint8_sub" ["uint8" "uint8"] [false false] "uint8"]
   ["UInt8.toFloat32" "lean_uint8_to_float32" ["uint8"] [false] "float32"]
   ["UInt8.toFloat" "lean_uint8_to_float" ["uint8"] [false] "float"]
   ["UInt8.toBitVec" "lean_uint8_to_nat" ["uint8"] [false] "tobject"]
   ["UInt8.toUInt16" "lean_uint8_to_uint16" ["uint8"] [false] "uint16"]
   ["UInt8.toUSize" "lean_uint8_to_usize" ["uint8"] [false] "usize"]
   ["UInt8.xor" "lean_uint8_xor" ["uint8" "uint8"] [false false] "uint8"]
   ["USize.complement" "lean_usize_complement" ["usize"] [false] "usize"]
   ["USize.div" "lean_usize_div" ["usize" "usize"] [false false] "usize"]
   ["USize.log2" "lean_usize_log2" ["usize"] [false] "usize"]
   ["USize.lor" "lean_usize_lor" ["usize" "usize"] [false false] "usize"]
   ["USize.mod" "lean_usize_mod" ["usize" "usize"] [false false] "usize"]
   ["USize.neg" "lean_usize_neg" ["usize"] [false] "usize"]
   ["USize.ofBitVec" "lean_usize_of_nat_mk" ["tobject"] [false] "usize"]
   ["USize.toFloat32" "lean_usize_to_float32" ["usize"] [false] "float32"]
   ["USize.toFloat" "lean_usize_to_float" ["usize"] [false] "float"]
   ["USize.toUInt16" "lean_usize_to_uint16" ["usize"] [false] "uint16"]
   ["USize.toUInt32" "lean_usize_to_uint32" ["usize"] [false] "uint32"]
   ["USize.toUInt8" "lean_usize_to_uint8" ["usize"] [false] "uint8"]
   ["USize.xor" "lean_usize_xor" ["usize" "usize"] [false false] "usize"]
  ])

(defn- typed-name [text]
  (reduce (fn [parent part] ["str" parent part]) ["anonymous"] (.split ^String text "\\.")))
(defn extern-row [[decl symbol params borrowed result]]
  (let [n (typed-name decl)]
    {"kind" "decl" "name" n "dependencies" [] "redirect" nil
     "runtime" {"role" "ordinary" "initializer" nil}
     "ir" {"extern" {"f" n "type" result
                     "xs" (mapv (fn [i ty borrow] {"x" {"idx" (inc i)} "ty" ty "borrow" borrow})
                                (range) params borrowed)
                     "ext" {"entries" [{"standard" {"backend" ["str" ["anonymous"] "all"] "fn" symbol}}]}}}}))
(def scalar? #{"uint8" "uint16" "uint32" "uint64" "usize" "float" "float32"})
(defn boxed-row
  "The shape Lean emits for `_boxed`: unbox and release scalar operands, release
   borrowed object operands after the call, box a scalar result."
  [[decl _ params borrowed result]]
  (let [n (count params) call (inc (* 2 n)) boxed (inc call)
        args (mapv (fn [i ty] (c/v (if (scalar? ty) (+ 1 n i) (inc i)))) (range) params)
        tail (if (scalar? result)
               ["vdecl" {:idx boxed} "tobject" {:box {:ty result :x {:idx call}}} (c/ret boxed)]
               (c/ret call))
        tail (reduce (fn [k i] (if (and (nth borrowed i) (not (scalar? (nth params i))))
                                 ["dec" {:idx (inc i)} 1 true false k] k))
                     tail (reverse (range n)))
        body (c/let-ir call (if (scalar? result) result "tobject")
               {:fap {:c (typed-name decl) :ys args}} tail)
        body (reduce (fn [k i] (let [ty (nth params i)]
                                 (if (scalar? ty)
                                   (c/let-ir (+ 1 n i) ty {:unbox {:x {:idx (inc i)}}}
                                     ["dec" {:idx (inc i)} 1 true false k])
                                   k)))
                     body (reverse (range n)))]
    {:kind "decl" :name (typed-name (str decl "._boxed"))
     :ir {:fdecl {:f (typed-name (str decl "._boxed")) :type "tobject" :body body
                  :xs (mapv #(c/p (inc %) "tobject") (range n))}}}))
(def wide #{"uint64" "usize"})
(defn helpers []
  (for [ty wide op [:box :unbox]]
    (if (= op :box)
      (c/decl (str "box-" ty) [(c/p 1 ty)] "object"
        (c/let-ir 2 "object" {:box {:ty ty :x {:idx 1}}} (c/ret 2)))
      (c/decl (str "unbox-" ty) [(c/p 1 "object")] ty
        (c/let-ir 2 ty {:unbox {:x {:idx 1}}} ["dec" {:idx 1} 1 true false (c/ret 2)])))))
(defn context []
  (assoc *basis* :program
         (j/invoke-static (:prepare *basis*)
                          [(x/raw (concat (map extern-row abis)
                                          (map boxed-row (remove (fn [[_ _ _ _ r]] (#{"float" "float32"} r)) abis))
                                          (helpers)))])))

;; Independent model: mathematical integers, then the declared result domain.
(def big biginteger)
(defn pow2 [bits] (.shiftLeft java.math.BigInteger/ONE (int bits)))
(defn wrap [bits n] (.mod (big n) (pow2 bits)))
(def widths {"uint8" 8 "uint16" 16 "uint32" 32 "uint64" 64 "usize" 64})
(defn emod [a b] (if (zero? b) a (mod a (abs b))))
(defn model [symbol args]
  (let [[a b] (map bigint args)]
    (if-let [[_ ty op] (re-matches #"lean_(uint8|uint16|uint32|uint64|usize)_(.*)" symbol)]
      (let [bits (widths ty) w #(wrap bits %)]
        (case op
          "add" (w (+ a b)) "sub" (w (- a b)) "mul" (w (* a b))
          "div" (if (zero? b) 0 (quot a b)) "mod" (if (zero? b) a (rem a b))
          "land" (.and (big a) (big b)) "lor" (.or (big a) (big b)) "xor" (.xor (big a) (big b))
          "complement" (w (- (dec (pow2 bits)) a)) "neg" (w (- a))
          "shift_left" (w (* a (pow2 (mod b bits)))) "shift_right" (quot a (pow2 (mod b bits)))
          "log2" (if (zero? a) 0 (dec (.bitLength (big a))))
          "dec_eq" (if (= a b) 1 0) "dec_lt" (if (< a b) 1 0) "dec_le" (if (<= a b) 1 0)
          "to_uint8" (wrap 8 a) "to_uint16" (wrap 16 a) "to_uint32" (wrap 32 a)
          "to_uint64" (wrap 64 a) "to_usize" (wrap 64 a) "to_nat" a "of_nat_mk" (w a)
          "to_float" (.doubleValue (big a)) "to_float32" (.floatValue (big a))))
      (case symbol
        ("lean_bool_to_uint8" "lean_bool_to_uint16" "lean_bool_to_uint32" "lean_bool_to_usize") a
        "lean_int_mul" (* a b)
        ("lean_int_div" "lean_int_div_exact") (if (zero? b) 0 (quot a b))
        "lean_int_mod" (if (zero? b) a (rem a b))
        "lean_int_ediv" (if (zero? b) 0 (/ (- a (emod a b)) b))
        "lean_int_emod" (emod a b)
        "lean_int_dec_nonneg" (if (neg? a) 0 1)
        "lean_nat_land" (.and (big a) (big b)) "lean_nat_lxor" (.xor (big a) (big b))
        "lean_nat_gcd" (.gcd (big a) (big b)) "lean_nat_pred" (max 0 (dec a))
        "lean_nat_div_exact" (if (zero? b) 0 (quot a b))))))

(defn carrier [n] (let [n (big n)] (if (<= (.bitLength n) 63) (.longValue n) n)))
(def huge (pow2 100))
(def int-values (mapv big [(- huge) (- (pow2 64)) (dec (big Long/MIN_VALUE)) Long/MIN_VALUE (- (pow2 62)) -7 -3 -1 0 1 2 3 7
                           (pow2 62) Long/MAX_VALUE (inc (big Long/MAX_VALUE)) (pow2 64) huge]))
(def nat-values (mapv big [0 1 2 3 12 18 255 (pow2 32) (pow2 62) Long/MAX_VALUE (inc (big Long/MAX_VALUE))
                           (dec (pow2 64)) (pow2 64) huge (* 3 huge)]))
(defn word-values [bits]
  (distinct (map #(wrap bits %) [0 1 2 3 7 (dec bits) bits (inc bits) (quot (pow2 bits) 2)
                                 (dec (quot (pow2 bits) 2)) (- (pow2 bits) 2) (dec (pow2 bits))])))
(defn domain [ty]
  (case ty "tobject" nat-values "erased" [0] (word-values (widths ty 8))))
(defn vectors [[decl symbol params _ _]]
  (cond
    (.startsWith ^String symbol "lean_bool_to_") [[0] [1]]
    (#{"lean_int_div_exact"} symbol) (for [a int-values b int-values] [(* a b) b 0])
    (#{"lean_nat_div_exact"} symbol) (for [a nat-values b nat-values] [(* a b) b 0])
    (.startsWith ^String symbol "lean_int_")
    (if (= 1 (count params)) (map vector int-values) (for [a int-values b int-values] [a b]))
    :else (reduce (fn [acc ty] (for [prefix acc v (domain ty)] (conj prefix v))) [[]] params)))
(defn expected [[_ symbol params _ result] args]
  (model symbol (take 2 (if (= "erased" (last params)) (butlast args) args))))
(defn same? [expected actual]
  (if (or (instance? Double actual) (instance? Float actual))
    (= (if (instance? Float actual) (Float/floatToRawIntBits expected) (Double/doubleToRawLongBits expected))
       (if (instance? Float actual) (Float/floatToRawIntBits actual) (Double/doubleToRawLongBits actual)))
    (= (big expected) (big actual))))
(defn symbol-of [row]
  (j/invoke-static (.getMethod ^Class (:class *basis*) "validateExternAbi" (into-array Class [java.util.Map])) [row]))
(def borrowed-int? (fn [[_ symbol]] (.startsWith ^String symbol "lean_int_")))

(deftest pinned-init-abis-validate-and-fixed-width-matrix-is-closed
  (is (= 85 (count abis)))
  (is (= (count abis) (count (set (map first abis)))))
  (doseq [abi abis]
    (is (= (second abi) (symbol-of (extern-row abi))) (first abi)))
  ;; Every Lean 4.33.1 Init word extern except signed IntN/ISize now resolves.
  (let [ops ["add" "sub" "mul" "div" "mod" "land" "lor" "xor" "complement" "neg" "shift_left"
             "shift_right" "log2" "dec_eq" "dec_lt" "dec_le"]]
    (doseq [ty ["uint8" "uint16" "uint32" "uint64" "usize"] op ops
            :let [unary (#{"complement" "neg" "log2"} op)
                  row (extern-row ["Probe" (str "lean_" ty "_" op) (if unary [ty] [ty ty])
                                   (if unary [false] [false false])
                                   (if (.startsWith ^String op "dec_") "uint8" ty)])]]
      (is (= (str "lean_" ty "_" op) (symbol-of row)))))
  (doseq [row [(assoc-in (extern-row (first (filter #(= "Int.mul" (first %)) abis))) ["ir" "extern" "xs" 0 "borrow"] false)
               (assoc-in (extern-row (first (filter #(= "UInt16.add" (first %)) abis))) ["ir" "extern" "type"] "uint32")
               (assoc-in (extern-row (first (filter #(= "Nat.gcd" (first %)) abis))) ["ir" "extern" "xs" 1 "ty"] "object")]]
    (is (re-find #"Captured extern ABI mismatch" (c/failure #(symbol-of row))))))

(deftest direct-calls-match-the-model-on-edge-vectors
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [abi (remove borrowed-int? abis) args (vectors abi)]
        (let [actual (j/call ctx engine (first abi) (mapv carrier args))]
          (is (same? (expected abi args) actual) (str (first abi) " " args))
          (when (and (instance? java.math.BigInteger actual) (#{"tobject"} (last abi)))
            (is (> (.bitLength ^java.math.BigInteger actual) 63) "Nat results stay canonical"))))
      (finally (j/close! ctx engine)))))

(defn boxed-call [ctx engine [decl _ params _ result] args]
  (let [arguments (mapv (fn [ty v] (if (wide ty) (j/call ctx engine (str "box-" ty) [(carrier v)]) (carrier v)))
                        params args)
        value (j/call ctx engine (str decl "._boxed") arguments)]
    (if (wide result) (j/call ctx engine (str "unbox-" result) [value]) value)))

(deftest genuine-boxed-wrappers-match-including-borrowed-int
  (let [ctx (context) engine (j/machine ctx)]
    (try
      (doseq [abi abis :when (not (#{"float" "float32"} (last abi))) args (vectors abi)]
        (let [actual (boxed-call ctx engine abi args)]
          (is (same? (expected abi args) actual) (str (first abi) "._boxed " args))
          (when (and (borrowed-int? abi) (= "tobject" (last abi)))
            (is (if (instance? Long actual) true (> (.bitLength ^java.math.BigInteger actual) 63))
                "Int results stay canonical"))))
      (finally (j/close! ctx engine)))))

(deftest borrowed-int-primitives-require-owning-wrappers
  (let [ctx (context)]
    (doseq [abi (filter borrowed-int? abis)]
      (let [engine (j/machine ctx)]
        (try
          (is (re-find #"Borrowed Int primitive"
                       (c/failure #(j/call ctx engine (first abi) (vec (repeat (count (nth abi 2)) 1))))))
          (is (re-find #"Borrowed Int primitive" (c/failure #(j/make-closure! ctx engine (first abi) []))))
          (finally (j/close! ctx engine)))))))

(deftest int-long-boundaries-promote-and-demote-exactly
  (let [ctx (context) engine (j/machine ctx)
        call #(j/call ctx engine (str %1 "._boxed") (mapv carrier %2))]
    (try
      (is (= (inc (big Long/MAX_VALUE)) (call "Int.tdiv" [Long/MIN_VALUE -1])))
      (is (= (inc (big Long/MAX_VALUE)) (call "Int.ediv" [Long/MIN_VALUE -1])))
      (is (= 0 (call "Int.tmod" [Long/MIN_VALUE -1])))
      (is (= 0 (call "Int.emod" [Long/MIN_VALUE -1])))
      (is (instance? java.math.BigInteger (call "Int.mul" [Long/MAX_VALUE 2])))
      (is (instance? Long (call "Int.mul" [(pow2 64) 0])))
      (is (instance? Long (call "Int.tdiv" [(pow2 64) (pow2 2)])))
      (is (= Long/MIN_VALUE (call "Int.mul" [(- (pow2 62)) 2])))
      (is (= 1 (call "Int.emod" [-7 -2])))
      (is (= -4 (call "Int.ediv" [-7 2])))
      (is (= 4 (call "Int.ediv" [-7 -2])))
      (is (= -1 (call "Int.tmod" [-7 2])))
      (is (= -7 (call "Int.tmod" [-7 0])))
      (is (= -7 (call "Int.emod" [-7 0])))
      (is (= 0 (call "Int.ediv" [(- huge) 0])))
      (finally (j/close! ctx engine)))))

(deftest invalid-operands-erased-proofs-and-resource-bounds-refuse
  (let [ctx (context)]
    (x/probe-failure! ctx "Nat.gcd" [-1 2] #"Invalid Nat")
    (x/probe-failure! ctx "Nat.pred" [(big -1)] #"Invalid Nat")
    (x/probe-failure! ctx "Nat.divExact" [4 2 1] #"proof requires erased placeholder")
    (x/probe-failure! ctx "Int.divExact._boxed" [4 2 1] #"proof requires erased placeholder")
    (x/probe-failure! ctx "Int.mul._boxed" ["bad" 1] #"Expected exact signed Int carrier")
    (x/probe-failure! ctx "Bool.toUInt16" [2] #"canonical Bool")
    (x/probe-failure! ctx "UInt16.add" [65536 0] #"outside 16-bit range")
    (x/probe-failure! ctx "USize.ofBitVec" [-1] #"Invalid Nat")
    (let [big-operand (pow2 9000000)]
      (x/probe-failure! ctx "Int.mul._boxed" [big-operand (.negate big-operand)] #"outside bounded runtime bit limit"))))

(defn check! [basis] (binding [*basis* basis] (run-tests 'java-ir-arithmetic-checks)))
