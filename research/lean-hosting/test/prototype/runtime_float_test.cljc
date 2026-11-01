(ns prototype.runtime-float-test
  (:refer-clojure :exclude [cast])
  (:require [prototype.native-scalar :as native]
            [prototype.runtime-float :as runtime]
            [prototype.machine :as m]
            [prototype.scalar :as scalar]
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(def world {:unchanged :world})
(defn evaluate [symbol value] (runtime/evaluate {} world symbol [value]))
(defn cast [symbol value] (second (evaluate symbol value)))

(deftest binary32-bitcasts-match-native-nan-canonicalization
  ;; Native preserves ±0, min subnormal and ±inf. Both bitcast directions
  ;; replace signaling/quiet/negative NaNs with the profile's positive qNaN.
  (doseq [[bits bytes] [[0 [0 0 0 0]] [2147483648 [0 0 0 128]]
                       [1 [1 0 0 0]] [1069547520 [0 0 192 63]]
                       [2139095040 [0 0 128 127]] [4286578688 [0 0 128 255]]
                       [2139169605 [69 35 129 127]] [2143363909 [69 35 193 127]]
                       [4290847557 [69 35 193 255]]]]
    (let [[after value] (evaluate "lean_float32_of_bits" bits)
          nan-bits? (> (mod bits 2147483648) 2139095040)]
      (is (= world after))
      (is (= (if nan-bits? [0 0 192 127] bytes) (scalar/float-bytes "float32" value)))
      (is (= (if nan-bits? 2143289344 bits) (cast "lean_float32_to_bits" value))))))

(deftest binary64-exact-bitcasts-and-portable-carrier-restriction
  (doseq [[bits bytes] [[0 [0 0 0 0 0 0 0 0]] [1 [1 0 0 0 0 0 0 0]]
                       [4503599627370495 [255 255 255 255 255 255 15 0]]]]
    (let [value (cast "lean_float_of_bits" bits)]
      (is (= bytes (scalar/float-bytes "float" value)))
      (is (= bits (cast "lean_float_to_bits" value)))))
  #?(:clj
     (doseq [[bits bytes] [[9223372036854775808N [0 0 0 0 0 0 0 128]]
                          [4609434218613702656N [0 0 0 0 0 0 248 63]]
                          [9218868437227405312N [0 0 0 0 0 0 240 127]]
                          [18442240474082181120N [0 0 0 0 0 0 240 255]]
                          [9218868437227479877N [69 35 1 0 0 0 240 127]]
                          [9221120237041165125N [69 35 1 0 0 0 248 127]]
                          [18444492273895940933N [69 35 1 0 0 0 248 255]]]]
       (let [value (cast "lean_float_of_bits" bits)
             nan-bits? (> (mod bits 9223372036854775808N) 9218868437227405312N)]
         (is (= (if nan-bits? [0 0 0 0 0 0 248 127] bytes) (scalar/float-bytes "float" value)))
         (is (= (if nan-bits? 9221120237041090560N bits) (cast "lean_float_to_bits" value)))))
     :cljs
     (do
       (is (thrown? js/Error (cast "lean_float_of_bits" 9007199254740992)))
       (doseq [bytes [[0 0 0 0 0 0 0 128] [0 0 0 0 0 0 240 127]
                     [69 35 1 0 0 0 240 127] [69 35 1 0 0 0 248 255]]]
         (let [value (scalar/float-from-bytes "float" bytes)]
           (is (= bytes (scalar/float-bytes "float" value)))
           (is (thrown? js/Error (cast "lean_float_to_bits" value))))))))

(deftest bitcasts-reject-invalid-carriers-and-calls
  (doseq [[symbol value] [["lean_float32_of_bits" -1] ["lean_float32_of_bits" 4294967296]
                          ["lean_float_of_bits" 1.5] ["lean_float_to_bits" "1.0"]]]
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) (evaluate symbol value))))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"arity"
        (runtime/evaluate {} world "lean_float_of_bits" [])))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Unsupported"
        (runtime/evaluate {} world "unknown_float" [0]))))

(deftest unsigned-conversions-round-to-target-width
  (is (= [world 0.0] (evaluate "lean_uint64_to_float" 0)))
  (is (= 4294967295.0 (cast "lean_uint32_to_float" 4294967295)))
  (is (= 4294967296.0 (cast "lean_uint32_to_float32" 4294967295)))
  (is (= 16777216.0 (cast "lean_uint64_to_float32" 16777217)))
  #?(:clj
     (do
       (is (= 18446744073709551616.0 (cast "lean_uint64_to_float" 18446744073709551615N)))
       (is (= 9007199254740992.0 (cast "lean_uint64_to_float" 9007199254740993N)))
       (is (= 9007199254740996.0 (cast "lean_uint64_to_float" 9007199254740995N)))
       ;; 2^60 + 2^36 + 1 lies just above a binary32 tie. First converting to
       ;; binary64 loses the +1 and incorrectly selects the lower even float.
       (is (= [1 0 128 93]
              (scalar/float-bytes "float32" (cast "lean_uint64_to_float32" 1152921573326323713N)))))
     :cljs
     (is (thrown? js/Error (cast "lean_uint64_to_float" 9007199254740992))))
  (doseq [[symbol value] [["lean_uint64_to_float" -1] ["lean_uint32_to_float" 4294967296]]]
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) (cast symbol value)))))

(deftest public-bitcasts-canonicalize-raw-storage-nans
  (is (= 2143289344 (cast "lean_float32_to_bits" (scalar/float-from-bytes "float32" [1 0 128 255]))))
  #?(:clj (is (= 9221120237041090560N
                (cast "lean_float_to_bits" (scalar/float-from-bytes "float" [1 0 0 0 0 0 240 255]))))))

(deftest empty-float-array-capacity-does-not-create-elements
  (let [ops {:allocate m/allocate :node m/node
             :replace-node (fn [world value node] (assoc-in world [:heap (:id value)] node))}]
    (doseq [capacity [0 16 #?(:clj 9223372036854775807N :cljs 9007199254740991)]]
      (let [before (m/world {})
            [after value] (runtime/evaluate ops before "lean_mk_empty_float_array" [capacity])]
        (is (= {:kind :float-array :tag 248 :fields [] :rc 1 :values []} (m/node after value)))
        (is (empty? (:heap before)))))
    (doseq [capacity [-1 0.5 #?(:clj 9223372036854775808N :cljs 9007199254740992)]]
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
            (runtime/evaluate ops (m/world {}) "lean_mk_empty_float_array" [capacity]))))))

(def native-arithmetic-cases
  [["float" "div" "0" "4024000000000000" "0"]
   ["float" "div" "3ff0000000000000" "0" "7ff0000000000000"]
   ["float" "div" "3ff0000000000000" "8000000000000000" "fff0000000000000"]
   ["float" "div" "0" "0" "fff8000000000000"]
   ["float" "div" "7ff0000000000000" "7ff0000000000000" "fff8000000000000"]
   ["float" "div" "1" "4000000000000000" "0"]
   ["float" "add" "8000000000000000" "8000000000000000" "8000000000000000"]
   ["float" "sub" "0" "8000000000000000" "0"]
   ["float" "mul" "7ff0000000000000" "0" "fff8000000000000"]
   ["float" "add" "7ff0000000000042" "fff8000000000073" "7ff8000000000042"]
   ["float" "add" "7ff8000000000042" "fff0000000000073" "7ff8000000000042"]
   ["float" "add" "3ff0000000000000" "fff0000000000073" "fff8000000000073"]
   ["float" "div" "7ff0000000000042" "fff8000000000073" "7ff8000000000042"]
   ["float32" "div" "0" "41200000" "0"]
   ["float32" "div" "3f800000" "0" "7f800000"]
   ["float32" "div" "3f800000" "80000000" "ff800000"]
   ["float32" "div" "0" "0" "ffc00000"]
   ["float32" "div" "7f800000" "7f800000" "ffc00000"]
   ["float32" "div" "1" "40000000" "0"]
   ["float32" "add" "80000000" "80000000" "80000000"]
   ["float32" "sub" "0" "80000000" "0"]
   ["float32" "mul" "7f800000" "0" "ffc00000"]
   ["float32" "add" "7f800042" "ffc00073" "7fc00042"]
   ["float32" "add" "7fc00042" "ff800073" "7fc00042"]
   ["float32" "add" "3f800000" "ff800073" "ffc00073"]
   ["float32" "div" "7f800042" "ffc00073" "7fc00042"]
   ["float32" "add" "4b800000" "3f800000" "4b800000"]
   ["float32" "mul" "3f800001" "3f800001" "3f800002"]
   ["float32" "div" "3f800000" "40400000" "3eaaaaab"]])

(defn hex-bytes [float-type hex]
  (let [size (* 2 (scalar/width float-type))
        padded (str (apply str (repeat (- size (count hex)) "0")) hex)]
    (mapv (fn [digits] #?(:clj (Integer/parseInt (apply str digits) 16)
                          :cljs (js/parseInt (apply str digits) 16)))
          (reverse (partition 2 padded)))))

(deftest arithmetic-matches-pinned-native-ieee-patterns
  ;; Generated from pinned lean.h inline operations, with volatile input values.
  (doseq [[float-type operation a b expected] native-arithmetic-cases]
    (let [symbol (str (if (= float-type "float") "lean_float_" "lean_float32_") operation)
          [after result] (runtime/evaluate {} world symbol
                           [(scalar/float-from-bytes float-type (hex-bytes float-type a))
                            (scalar/float-from-bytes float-type (hex-bytes float-type b))])]
      (is (= world after))
      (is (= (hex-bytes float-type expected) (scalar/float-bytes float-type result))
          (str symbol " " a " " b)))))

(deftest negation-preserves-signaling-nan-payload-and-signed-zero
  (doseq [[float-type zero negative-zero positive-nan negative-nan]
          [["float" "0" "8000000000000000" "7ff0000000000042" "fff0000000000042"]
           ["float32" "0" "80000000" "7f800042" "ff800042"]]
          [input expected] [[zero negative-zero] [negative-zero zero]
                            [positive-nan negative-nan] [negative-nan positive-nan]]]
    (let [symbol (if (= float-type "float") "lean_float_negate" "lean_float32_negate")
          result (cast symbol (scalar/float-from-bytes float-type (hex-bytes float-type input)))]
      (is (= (hex-bytes float-type expected) (scalar/float-bytes float-type result))))))

(deftest ordered-comparisons-match-c-and-do-not-use-host-nan-equality
  (doseq [[float-type prefix nan-bits]
          [["float" "lean_float_" "7ff0000000000042"] ["float32" "lean_float32_" "7f800042"]]]
    (let [nan (scalar/float-from-bytes float-type (hex-bytes float-type nan-bits))]
      (doseq [operation ["beq" "decLe" "decLt"] a [nan 1.0] b [nan 1.0]
              :when (or (map? a) (map? b))]
        (is (= [world 0] (runtime/evaluate {} world (str prefix operation) [a b]))))
      (doseq [[operation a b expected] [["beq" 0.0 -0.0 1] ["beq" 1.0 2.0 0]
                                       ["decLe" 1.0 1.0 1] ["decLt" 1.0 1.0 0]
                                       ["decLe" -2.0 1.0 1] ["decLt" -2.0 1.0 1]
                                       ["decLt" ##Inf ##Inf 0] ["beq" ##Inf ##Inf 1]
                                       ["decLe" ##-Inf ##Inf 1]]]
        (is (= [world expected] (runtime/evaluate {} world (str prefix operation) [a b])))))))

(deftest arithmetic-validates-width-carriers-and-arity
  ;; Float32 arguments are rounded before the operation, independently of results.
  (is (= 0.0 (second (runtime/evaluate {} world "lean_float32_sub" [16777217 16777216]))))
  (doseq [[symbol args] [["lean_float_div" [1]] ["lean_float32_negate" [1 2]]
                         ["lean_float_add" ["1" 2]]
                         ["lean_float32_add" [(scalar/float-from-bytes "float" [1 0 0 0 0 0 240 127]) 2]]]]
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                 (runtime/evaluate {} world symbol args)))))

(deftest native-immediates-are-interpreted-at-the-floating-abi-boundary
  (doseq [[symbol n] [["lean_uint32_to_float" 4294967295]
                      ["lean_uint32_to_float32" 4294967295]
                      ["lean_uint64_to_float" 16777217]
                      ["lean_uint64_to_float32" 16777217]
                      ["lean_float32_of_bits" 1069547520]
                      ["lean_float_of_bits" 4503599627370495]]]
    (let [type (if (contains? #{"lean_uint32_to_float32" "lean_uint64_to_float32" "lean_float32_of_bits"} symbol) "float32" "float")]
      (is (= (scalar/float-bytes type (cast symbol n))
             (scalar/float-bytes type (cast symbol (native/native-scalar n)))))))
  (let [ops {:allocate m/allocate :node m/node
             :replace-node (fn [world value node] (assoc-in world [:heap (:id value)] node))}
        before (m/world {})
        [after ref] (runtime/evaluate ops before "lean_mk_empty_float_array" [(native/native-scalar 16)])
        [boxed mpz] (m/allocate before :mpz 250 [])
        boxed (assoc-in boxed [:heap (:id mpz) :integer] 16)]
    (is (= [] (:values (m/node after ref))))
    (is (empty? (:heap before)))
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
          (runtime/evaluate ops boxed "lean_mk_empty_float_array" [mpz])))))
