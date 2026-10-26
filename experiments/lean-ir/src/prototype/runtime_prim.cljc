(ns prototype.runtime-prim
  "Raw guest primitives. Arguments retain IR erased/proof/world positions.
   Heap ownership is logical; ops must provide snapshot-local replacement."
  (:require [prototype.scalar :as scalar]
            [prototype.native-scalar :as native]
            [prototype.runtime-string :as string]
            [prototype.runtime-object :as object]
            [prototype.runtime-float :as float]
            [prototype.runtime-thunk :as thunk]
            [prototype.runtime-task :as task]
            [prototype.runtime-expr :as expr]
            [prototype.runtime-expr-transform :as transform]
            [prototype.runtime-expr-bvars :as bvars]
            [prototype.runtime-expr-search :as search]
            [prototype.runtime-expr-replace :as expr-replace]
            [prototype.runtime-sharecommon :as sharecommon]
            [prototype.runtime-mvars :as mvars]
            [prototype.runtime-expr-mvars :as expr-mvars]
            [prototype.runtime-io :as io]
            [prototype.runtime-sync :as sync]
            [prototype.runtime-heartbeat :as heartbeat]))

(defn- fail [message data] (throw (ex-info message data)))
(defn- exact! [x]
  (when-not (and (integer? x) #?(:clj true :cljs (js/Number.isSafeInteger x)))
    (fail "Runtime integer outside exact host range" {:value x})) x)
(defn- nat! [x]
  (let [x (if (native/native-scalar? x) (native/nat-value x) x)]
    (exact! x) (when (neg? x) (fail "Expected Nat" {:value x})) x))
(defn- add [a b] (exact! #?(:clj (+' a b) :cljs (+ a b))))
(defn- mul [a b] (exact! #?(:clj (*' a b) :cljs (* a b))))
(defn- negate [a] (exact! #?(:clj (-' a) :cljs (- a))))
(defn- pow2 [n] #?(:clj (bigint (.shiftLeft java.math.BigInteger/ONE (int n)))
                     :cljs (js/Math.pow 2 n)))
(defn- unsigned [type x]
  (exact! x)
  (let [modulus (pow2 (* 8 (scalar/width type)))
        wrapped #?(:clj (mod x modulus)
                   :cljs (let [remainder (rem x modulus)]
                           ;; cljs mod adds the modulus even for positive inputs,
                           ;; losing small values when the modulus is 2^64.
                           (if (neg? remainder) (exact! (+ remainder modulus)) remainder)))]
    (scalar/integer! type wrapped)))
(defn- bits [operation a b]
  #?(:clj (bigint (case operation
                   :and (.and (biginteger a) (biginteger b))
                   :or (.or (biginteger a) (biginteger b))
                   :xor (.xor (biginteger a) (biginteger b))))
     :cljs (loop [a (nat! a) b (nat! b) power 1 result 0]
             (if (and (zero? a) (zero? b)) (exact! result)
               (recur (quot a 2) (quot b 2) (* power 2)
                      (+ result (if (case operation :and (and (odd? a) (odd? b))
                                                    :or (or (odd? a) (odd? b))
                                                    :xor (not= (odd? a) (odd? b))) power 0)))))))
(defn- shift-right [a n]
  #?(:clj (if (>= n (.bitLength (biginteger a))) 0
            (bigint (.shiftRight (biginteger a) (int n))))
     :cljs (if (>= n 53) 0 (quot a (pow2 n)))))
(defn- power [a n]
  (loop [a a n n result 1]
    (if (zero? n) result
      (let [result (if (odd? n) (mul result a) result) n (quot n 2)]
        (recur (if (zero? n) a (mul a a)) n result)))))

(def ^:private scalar-operations
  {"lean_nat_add" :add "lean_nat_sub" :nat-sub "lean_nat_mul" :mul
   "lean_nat_div" :div "lean_nat_div_exact" :div-exact "lean_nat_mod" :mod "lean_nat_pow" :pow "lean_nat_gcd" :gcd
   "lean_nat_land" :and "lean_nat_lor" :or "lean_nat_xor" :xor
   "lean_nat_shiftl" :shl "lean_nat_shiftr" :shr "lean_nat_dec_eq" :eq "lean_nat_dec_lt" :lt "lean_nat_dec_le" :le
   "lean_int_add" :add "lean_int_sub" :sub "lean_int_mul" :mul
   "lean_int_div" :div "lean_int_mod" :mod "lean_int_div_exact" :div-exact
   "lean_int_ediv" :ediv "lean_int_emod" :emod
   "lean_int_neg" :neg "lean_int_dec_lt" :lt "lean_int_dec_le" :le "lean_int_dec_eq" :eq
   "lean_nat_abs" :abs "lean_nat_to_int" :identity
   "lean_usize_add" :add "lean_usize_sub" :sub "lean_usize_mul" :mul
   "lean_usize_land" :and "lean_usize_shift_left" :shl "lean_usize_shift_right" :shr
   "lean_usize_dec_eq" :eq "lean_usize_dec_lt" :lt "lean_usize_dec_le" :le
   "lean_usize_of_nat" :from-nat "lean_usize_to_nat" :identity
   "lean_uint8_to_nat" :identity "lean_uint16_to_nat" :identity
   "lean_uint32_to_nat" :identity "lean_uint64_to_nat" :identity
   "lean_uint8_of_nat_mk" :from-nat "lean_uint16_of_nat_mk" :from-nat
   "lean_uint32_of_nat_mk" :from-nat "lean_uint64_of_nat_mk" :from-nat "lean_usize_of_nat_mk" :from-nat
   "lean_uint8_of_nat" :from-nat "lean_uint16_of_nat" :from-nat
   "lean_uint8_dec_eq" :eq "lean_uint8_dec_le" :le "lean_uint8_land" :and
   "lean_uint32_dec_eq" :eq "lean_uint32_dec_lt" :lt "lean_uint32_dec_le" :le "lean_uint32_of_nat" :from-nat "lean_uint32_add" :add
   "lean_uint32_to_uint8" :to-u8
   "lean_uint64_dec_eq" :eq "lean_uint64_dec_lt" :lt "lean_uint64_of_nat" :from-nat
   "lean_uint64_add" :add "lean_uint64_sub" :sub "lean_uint64_mul" :mul
   "lean_uint64_land" :and "lean_uint64_lor" :or "lean_uint64_shift_left" :shl
   "lean_uint64_xor" :xor "lean_uint64_shift_right" :shr "lean_uint64_to_usize" :identity})

(def unsigned-casts
  (merge
    (into {} (for [source ["uint8" "uint16" "uint32" "uint64" "usize"]
                   target ["uint8" "uint16" "uint32" "uint64" "usize"]
                   :when (not= source target)]
               [(str "lean_" source "_to_" target) {:source source :target target :arity 1}]))
    ;; Bool is an unboxed uint8_t in this ABI, including signed-result carriers.
    (into {} (for [[suffix target] [["uint8" "uint8"] ["uint16" "uint16"]
                                    ["uint32" "uint32"] ["uint64" "uint64"] ["usize" "usize"]
                                    ["int8" "uint8"] ["int16" "uint16"] ["int32" "uint32"]
                                    ["int64" "uint64"] ["isize" "usize"]]]
               [(str "lean_bool_to_" suffix) {:source "uint8" :target target :arity 1}]))))

(def fixed-signed-operations
  ;; Lean stores signed fixed-width integers in unsigned IR carriers. These
  ;; operations preserve the two's-complement bits (lean.h SInt intrinsics).
  (into {} (for [[prefix type] [["int8" "uint8"] ["int16" "uint16"]
                                ["int32" "uint32"] ["int64" "uint64"] ["isize" "usize"]]
                 [suffix operation arity] [["of_nat" :from-nat 1] ["of_int" :from-int 1] ["to_int" :to-int 1] ["neg" :neg 1]
                                            ["add" :add 2] ["sub" :sub 2] ["mul" :mul 2]]]
             [(str "lean_" prefix "_" suffix) {:operation operation :type type :arity arity}])))

(def pinned-build
  ;; The importer admits exactly this producer version/profile. These are guest
  ;; compiler metadata, never the JVM host's Clojure/JDK version.
  {"lean_system_platform_windows" 0 "lean_system_platform_osx" 0
   "lean_system_platform_emscripten" 0
   "lean_system_platform_target" "x86_64-unknown-linux-gnu"
   ;; Pinned lean.h:3296–3309. These return the exclusive constructor-field
   ;; and scalar-size limits, inclusive tag limit, and guest sizeof(size_t).
   ;; Ignore the owned Unit argument exactly as the native inline functions do.
   "lean_get_max_ctor_fields" 256 "lean_get_max_ctor_scalars_size" 1024
   "lean_get_max_ctor_tag" 243 "lean_get_usize_size" 8
   ;; runtime/object.cpp:2804 and lean.h:31, not the JVM closure ABI.
   "lean_closure_max_args" 16
   "lean_manual_get_root" "https://lean-lang.org/doc/reference/4.33.1/"
   "lean_version_get_major" 4 "lean_version_get_minor" 33
   "lean_version_get_patch" 1 "lean_version_get_is_release" 1
   "lean_version_get_special_desc" ""
   "lean_get_githash" "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"})

(def ^:private arities
  {"lean_uint8_to_nat" 1 "lean_uint16_to_nat" 1 "lean_uint32_to_nat" 1 "lean_uint64_to_nat" 1
   "lean_uint8_of_nat_mk" 1 "lean_uint16_of_nat_mk" 1 "lean_uint32_of_nat_mk" 1
   "lean_uint64_of_nat_mk" 1 "lean_usize_of_nat_mk" 1
   "lean_ptr_addr" 2 "lean_max_small_nat" 1
   "lean_libuv_version" 1 "lean_openssl_version" 1
   "lean_get_leanc_extra_flags" 1 "lean_get_leanc_internal_flags" 1
   "lean_get_linker_flags" 1 "lean_get_internal_linker_flags" 1
   "lean_internal_get_build_type" 1
   "lean_internal_has_llvm_backend" 1 "lean_internal_get_default_verbose" 1 "lean_internal_get_believer_trust_level" 1 "lean_internal_is_multi_thread" 1
   "lean_internal_get_default_max_memory" 1 "lean_internal_get_default_max_heartbeat" 1
   "prototype_task_map_context" 2
   "lean_task_pure" 2 "lean_task_get_own" 2 "lean_task_map" 6
   "lean_array_get" 4 "lean_array_get_borrowed" 4
   "lean_array_fget" 4 "lean_array_fget_borrowed" 4
   "lean_array_uget" 4 "lean_array_uget_borrowed" 4
   "lean_array_get_size" 2 "lean_array_size" 2
   "lean_mk_empty_array_with_capacity" 2 "lean_array_push" 3
   "lean_array_fset" 5 "lean_array_uset" 5 "lean_array_fswap" 6
   "lean_array_set" 4 "lean_array_pop" 2 "lean_mk_array" 3 "lean_array_mk" 2 "lean_array_to_list" 2
   "lean_st_mk_ref" 4 "lean_st_ref_get" 4 "lean_st_ref_take" 4 "lean_st_ref_set" 5 "lean_st_ref_swap" 5
   "lean_int_neg" 1 "lean_nat_abs" 1 "lean_nat_to_int" 1
   "lean_nat_div_exact" 3 "lean_int_div_exact" 3
   "lean_profileit" 5 "lean_void_mk" 2
   "lean_usize_to_nat" 1 "lean_uint32_to_uint8" 1 "lean_uint64_to_usize" 1
   "lean_uint32_of_nat" 2 "lean_system_platform_nbits" 1 "lean_io_initializing" 1})

(def supported-symbols
  (merge (update-vals unsigned-casts #(select-keys % [:arity])) (update-vals fixed-signed-operations #(select-keys % [:arity])) (zipmap (keys pinned-build) (repeat {:arity 1})) string/supported-symbols object/supported-symbols float/supported-symbols thunk/supported-symbols expr/supported-symbols transform/supported-symbols bvars/supported-symbols search/supported-symbols expr-replace/supported-symbols sharecommon/supported-symbols expr-mvars/supported-symbols mvars/supported-symbols io/supported-symbols sync/supported-symbols heartbeat/supported-symbols (into {} (map (fn [[symbol _]] [symbol {:arity (get arities symbol 2)}]) scalar-operations))
         (into {} (map (fn [[symbol n]] [symbol {:arity n}]) arities))
         task/supported-symbols
         {"lean_uint8_of_nat" {:arities #{1 2}}
          "lean_uint16_of_nat" {:arities #{1 2}}
          "lean_uint32_of_nat" {:arities #{1 2}}
          "lean_usize_of_nat" {:arities #{1 2}}
          "lean_uint64_of_nat" {:arities #{1 2}}}))

(defn- node! [ops world ref kind]
  (when-not ((:ref? ops) ref) (fail "Expected guest heap reference" {:value ref :kind kind}))
  (let [node ((:node ops) world ref)]
    (when-not (= kind (:kind node)) (fail "Incorrect runtime object kind" {:expected kind :node node}))
    (update node :fields vec)))
(defn- borrowed-node!
  ;; Read-only consumers may borrow a backend's fields without materializing an
  ;; immutable copy. The node and its storage must never escape this operation.
  [ops world ref kind]
  (when-not ((:ref? ops) ref) (fail "Expected guest heap reference" {:value ref :kind kind}))
  (let [node ((or (:borrow-node ops) (:node ops)) world ref)]
    (when-not (= kind (:kind node))
      (fail "Incorrect runtime object kind" {:expected kind :actual (:kind node)}))
    node))
(defn- retain [ops world value n] (if (pos? n) ((:retain ops) world value n) world))
(defn- release [ops world value] ((:release ops) world value 1))
(defn- exclusive-array [ops world ref]
  (let [node (node! ops world ref :array)]
    (if (= 1 (:rc node)) [world ref node]
      (let [world (reduce #(retain ops %1 %2 1) world (:fields node))
            [world copy] ((:allocate ops) world :array 246 (:fields node))]
        [(release ops world ref) copy (node! ops world copy :array)]))))
(defn- replace-fields [ops world ref _node fields]
  ;; Releasing an old ref value can decrement this same ref through a cycle.
  ;; Preserve the resulting count rather than restoring an earlier node snapshot.
  ((:replace-node ops) world ref (assoc ((:node ops) world ref) :fields (vec fields))))
(defn- set-array-field [ops world ref index value]
  (let [borrowed (borrowed-node! ops world ref :array)]
    (if (and (= 1 (:rc borrowed)) (:store-array-field! ops))
      (let [old (nth (:fields borrowed) (int index))
            world (release ops world old)]
        [((:store-array-field! ops) world ref (int index) value) ref])
      (let [[world array node] (exclusive-array ops world ref)
            fields (:fields node)
            world (release ops world (nth fields (int index)))]
        [(replace-fields ops world array node (assoc fields (int index) value)) array]))))
(defn- index! [fields i]
  (let [i (nat! i)]
    (when-not (< i (count fields)) (fail "Guest array index out of bounds" {:index i :size (count fields)}))
    (int i)))
(defn- size! [n]
  (let [n (nat! n)]
    (when (> n 2147483647) (fail "Guest array exceeds supported host size" {:size n})) (int n)))

(defn- quotient [a b]
  ;; Host Long.MIN_VALUE / -1 must widen, like Lean's arbitrary precision Int.
  (if (zero? b) 0
    #?(:clj (if (and (= a Long/MIN_VALUE) (= b -1)) (quot (bigint a) (bigint b)) (quot a b))
       :cljs (quot a b))))

(defn- exact-quotient [a b]
  ;; Lean's third, erased proof establishes divisibility. The optimized native
  ;; mpz implementation assumes it; reject invalid raw calls rather than emulate
  ;; undefined divexact behavior. 0/0 is a valid divisible pair and yields zero.
  (when (if (zero? b) (not (zero? a)) (not (zero? (rem a b))))
    (fail "Exact division requires a divisible pair" {:numerator a :denominator b}))
  (quotient a b))

(defn- numeric [ops world #?(:clj ^String symbol :cljs symbol) args]
  (let [operation (or (get scalar-operations symbol) (get-in fixed-signed-operations [symbol :operation]))
        type (or (get-in fixed-signed-operations [symbol :type]) (cond (.startsWith symbol "lean_usize_") "usize"
                   (.startsWith symbol "lean_uint8_") "uint8"
                   (.startsWith symbol "lean_uint16_") "uint16"
                   (.startsWith symbol "lean_uint32_") "uint32"
                   (.startsWith symbol "lean_uint64_") "uint64"))
        nat-input? (or (and (.startsWith symbol "lean_nat_") (not= operation :abs))
                       (= operation :from-nat))
        unary? (contains? #{:identity :neg :abs :from-nat :from-int :to-int :to-u8} operation)
        operands (take (if unary? 1 2) args)
        [a b] (mapv #(cond nat-input? (nat! (native/number-value ops world %))
                           (and type (not= operation :from-int)) (scalar/integer! type %)
                           :else (exact! (native/int-value ops world %))) operands)
        result (case operation
                 :add (add a b) :sub (add a (negate b)) :nat-sub (max 0 (add a (negate b)))
                 :mul (mul a b) :div (quotient a b) :div-exact (exact-quotient a b)
                 :mod (if (zero? b) a (rem a b)) :pow (power a b)
                 :ediv (let [q (quotient a b)]
                         (if (and (not (zero? b)) (neg? (rem a b)))
                           (add q (if (pos? b) -1 1)) q))
                 :emod (if (zero? b) a
                         (let [r (rem a b)]
                           (if (neg? r) (add r (if (pos? b) b (negate b))) r)))
                 :gcd (loop [left a right b]
                        (if (zero? right) left (recur right (rem left right))))
                 :eq (if (= a b) 1 0) :lt (if (< a b) 1 0) :le (if (<= a b) 1 0)
                 :and (bits :and a b) :or (bits :or a b) :xor (bits :xor a b)
                 :shr (shift-right a (if type (mod b (* 8 (scalar/width type))) b))
                  :shl (let [count (if type (mod b (* 8 (scalar/width type))) b)]
                        (cond (zero? a) 0
                              (> count 2147483647) (fail "Nat shift exceeds supported host allocation" {:count count})
                              :else (mul a (pow2 count))))
                 :identity a :neg (negate a) :abs (if (neg? a) (negate a) a)
                 :from-nat a :from-int a
                 :to-int (let [modulus (pow2 (* 8 (scalar/width type)))]
                           (if (>= a (quot modulus 2)) (add a (negate modulus)) a))
                 :to-u8 (unsigned "uint8" a))]
    (if (and type (not (contains? #{:eq :lt :le :identity :to-int :to-u8} operation)))
      (unsigned type result) (exact! result))))

(def ^:private ffi-build-queries
  #{"lean_get_leanc_extra_flags" "lean_get_leanc_internal_flags"
    "lean_get_linker_flags" "lean_get_internal_linker_flags"
    "lean_internal_get_build_type"})

(defn- ffi-build-query [ops world symbol args]
  (let [provider (:runtime-build ops)]
    (when-not (ifn? provider)
      (fail "Missing explicit guest runtime build capability" {:symbol symbol}))
    (let [entry (provider world symbol)
          flags (if (= symbol "lean_get_linker_flags")
                  (let [selector (if (zero? (scalar/integer! "uint8" (first args))) :shared :static)]
                    (when-not (and (map? entry) (contains? entry selector))
                      (fail "Missing selected guest linker flags metadata" {:selector selector}))
                    (get entry selector))
                  entry)]
      (when-not (string? flags)
        (fail "Expected guest compiler/linker build String metadata" {:symbol symbol}))
      ;; Pinned util/ffi.cpp and runtime/platform.cpp return configured C strings.
      ;; Keep exact bytes/spaces and ROOT markers; execute no compiler/linker.
      (when-not (= -1 (.indexOf ^String flags "\u0000"))
        (fail "Compiler/linker build metadata contains NUL" {:symbol symbol}))
      (string/evaluate {} world "lean_string_utf8_byte_size" [flags])
      [world flags])))

(def ^:private numeric-build-queries
  {"lean_libuv_version" :uint32 "lean_openssl_version" :uint32
   "lean_internal_get_believer_trust_level" :uint32 "lean_internal_is_multi_thread" :bool
   "lean_internal_has_llvm_backend" :bool "lean_internal_get_default_verbose" :bool
   "lean_internal_get_default_max_memory" :nat "lean_internal_get_default_max_heartbeat" :nat})

(defn- numeric-build-query [ops world symbol]
  (let [provider (:runtime-build ops)]
    (when-not (ifn? provider)
      (fail "Missing explicit guest runtime build capability" {:symbol symbol}))
    (let [value (provider world symbol)]
      (when-not (integer? value)
        (fail "Expected exact guest runtime build numeric metadata" {:symbol symbol}))
      [world
       (case (get numeric-build-queries symbol)
         :uint32 (scalar/integer! "uint32" value)
         :bool (do (when-not (contains? #{0 1} value)
                     (fail "Expected guest runtime build Bool metadata" {:symbol symbol})) value)
         :nat (let [value (native/nat-value value)]
                ;; Pinned memory.cpp/interrupt.cpp use lean_box(default), not
                ;; an allocating arbitrary-Nat conversion. Units stay native
                ;; MiB / thousands of heartbeats; this sets no hosted limits.
                (when (> value #?(:clj 9223372036854775807N :cljs js/Number.MAX_SAFE_INTEGER))
                  (fail "Guest runtime build Nat exceeds exact tagged profile" {:symbol symbol})) value))])))

(defn evaluate
  "Evaluate a supported extern using complete IR arguments and injected heap ops.
   Bounds violations fail explicitly; no native panic logging/default policy is emulated."
  [ops world #?(:clj ^String symbol :cljs symbol) args]
  (let [spec (or (get supported-symbols symbol) (get thunk/internal-symbols symbol) (get task/internal-symbols symbol) (get mvars/internal-symbols symbol) (get expr-mvars/internal-symbols symbol) (get search/internal-symbols symbol) (get expr-replace/internal-symbols symbol)) n (count args)]
    (when-not spec (fail "Unsupported runtime extern" {:symbol symbol}))
    (when-not (if-let [arities (:arities spec)] (contains? arities n) (= (:arity spec) n))
      (fail "Runtime extern arity mismatch" {:symbol symbol :count n :spec spec})))
  (cond
    (= symbol "lean_void_mk")
    ;; Pinned lean.h: consume the owned payload and return the erased ST state.
    ;; The native lean_box(0) is represented by the IR void/world token here.
    [((:release ops) world (second args) 1) :prototype.machine/erased]
    (contains? unsigned-casts symbol)
    (let [{:keys [source target]} (get unsigned-casts symbol)]
      [world (unsigned target (scalar/integer! source (first args)))])
    (contains? ffi-build-queries symbol) (ffi-build-query ops world symbol args)
    (contains? numeric-build-queries symbol) (numeric-build-query ops world symbol)
    (contains? pinned-build symbol) [world (get pinned-build symbol)]
    (contains? string/supported-symbols symbol) (string/evaluate ops world symbol args)
    (contains? object/supported-symbols symbol) (object/evaluate ops world symbol args)
    (contains? float/supported-symbols symbol) (float/evaluate ops world symbol args)
    (or (contains? thunk/supported-symbols symbol) (contains? thunk/internal-symbols symbol))
    (thunk/evaluate ops world symbol args)
    (or (contains? task/supported-symbols symbol) (contains? task/internal-symbols symbol))
    (task/evaluate ops world symbol args)
    (contains? expr/supported-symbols symbol) (expr/evaluate ops world symbol args)
    (contains? sharecommon/supported-symbols symbol) (sharecommon/evaluate ops world symbol args)
    (contains? expr-replace/internal-symbols symbol) (expr-replace/evaluate ops world symbol args)
    (contains? search/internal-symbols symbol) (search/evaluate ops world symbol args)
    (contains? transform/supported-symbols symbol) (transform/evaluate ops world symbol args)
    (contains? bvars/supported-symbols symbol) (bvars/evaluate ops world symbol args)
    (or (contains? mvars/supported-symbols symbol) (contains? mvars/internal-symbols symbol))
    (mvars/evaluate ops world symbol args)
    (or (contains? expr-mvars/supported-symbols symbol) (contains? expr-mvars/internal-symbols symbol))
    (expr-mvars/evaluate ops world symbol args)
    (contains? io/supported-symbols symbol) (io/evaluate ops world symbol args)
    (contains? sync/supported-symbols symbol) (sync/evaluate ops world symbol args)
    (contains? heartbeat/supported-symbols symbol) (heartbeat/evaluate ops world symbol args)
    (or (contains? scalar-operations symbol) (contains? fixed-signed-operations symbol))
    (let [argument (first args)
          mpz? (and (:ref? ops) ((:ref? ops) argument)
                    (= :mpz (:kind ((:node ops) world argument))))]
      (cond
        ;; Native Nat.toInt consumes and transfers a boxed MPZ unchanged.
        (and mpz? (= symbol "lean_nat_to_int"))
        (do (native/nat-value ops world argument) [world argument])
        :else
        (let [result (numeric ops world symbol args)
              world (if (and (.endsWith symbol "_of_nat_mk") mpz?)
                      ((:release ops) world argument 1) world)]
          [world result])))
    :else (let [[_ a b c] args
                ;; Normalize only ABI positions known to be Nat/indices. Other
                ;; erased object fields retain their native scalar carriers.
                a (if (contains? #{"lean_mk_empty_array_with_capacity" "lean_mk_array"} symbol)
                    (native/nat-value ops world a) a)
                b (cond
                    (contains? #{"lean_array_uget" "lean_array_uget_borrowed" "lean_array_uset"} symbol)
                    (scalar/integer! "usize" b)
                    (contains? #{"lean_array_fget" "lean_array_fget_borrowed" "lean_array_fset"
                                 "lean_array_fswap" "lean_array_set"} symbol)
                    (native/nat-value ops world b)
                    :else b)
                c (if (contains? #{"lean_array_get" "lean_array_get_borrowed" "lean_array_fswap"} symbol)
                    (native/nat-value ops world c) c)]
      (case symbol
        "lean_ptr_addr" [world ((:pointer-address ops) world a)]
        "lean_max_small_nat"
        ;; object.cpp:2808 returns SIZE_MAX>>1 from the pinned64-bit guest.
        ;; JS Number cannot represent this Nat; never substitute a smaller limit.
        #?(:clj [world 9223372036854775807N]
           :cljs (fail "Guest maxSmallNat requires an exact 64-bit integer backend" {}))
        "prototype_task_map_context"
        (let [[priority sync] args]
          (let [priority (native/nat-value ops world priority)]
            (when (> priority #?(:clj 9223372036854775807N :cljs 9007199254740991))
              (fail "Task priority must be a native small Nat" {:priority priority})))
          (scalar/integer! "uint8" sync)
          [world 0])
        "lean_task_pure" ((:allocate ops) world :task 252 [a])
        "lean_task_get_own"
        (let [task (node! ops world a :task)]
          (when-not (= 1 (count (:fields task))) (fail "Malformed resolved task" {:task a}))
          (let [v (first (:fields task))]
            [((:release ops) ((:retain ops) world v 1) a 1) v]))
        "lean_task_map" (fail "Task.map requires explicit guest callback lowering" {})
        "lean_system_platform_nbits" [world 64]
        "lean_io_initializing"
        (let [initializing? (:initializing? ops)]
          (when-not initializing? (fail "Missing guest initialization context" {:symbol symbol}))
          [world (if (initializing? world) 1 0)])
        "lean_mk_empty_array_with_capacity"
        (do (size! a) ((:allocate ops) world :array 246 []))
        ("lean_array_size" "lean_array_get_size")
        [world (count (:fields (borrowed-node! ops world a :array)))]
        ("lean_array_fget" "lean_array_uget" "lean_array_fget_borrowed" "lean_array_uget_borrowed"
         "lean_array_get" "lean_array_get_borrowed")
        (let [[array index] (if (contains? #{"lean_array_get" "lean_array_get_borrowed"} symbol) [b c] [a b])
              fields (:fields (borrowed-node! ops world array :array))
              value (nth fields (index! fields index))]
          [(if (.endsWith symbol "_borrowed") world (retain ops world value 1)) value])
        "lean_array_set"
        (let [fields (:fields (borrowed-node! ops world a :array))
              boxed-index? ((:ref? ops) (nth args 2))]
          ;; lean.h:1064 checks scalar-ness before the bounds check. Native
          ;; set_panic drops the new value and can return the original array;
          ;; this prototype explicitly traps before any ownership/allocation
          ;; change instead of emulating native panic logging/default behavior.
          (when (or boxed-index? (not (< b (count fields))))
            (fail "Array.set! index out of bounds: native panic path unsupported"
                  {:index b :size (count fields) :runtime-limit :native-panic}))
          (set-array-field ops world a b c))
        ("lean_array_fset" "lean_array_uset")
        (let [fields (:fields (borrowed-node! ops world a :array))]
          (index! fields b)
          (set-array-field ops world a b c))
        ("lean_array_push" "lean_array_pop" "lean_array_fswap")
        (let [_ (when (contains? #{"lean_array_fset" "lean_array_uset" "lean_array_fswap"} symbol)
                  (let [fields (:fields (node! ops world a :array))]
                    (index! fields b) (when (= symbol "lean_array_fswap") (index! fields c))))
              [world array node] (exclusive-array ops world a)
              fields (:fields node)
              [world fields] (case symbol
                               "lean_array_push" [world (conj fields b)]
                               "lean_array_pop" (if (empty? fields) [world fields]
                                                  [(release ops world (peek fields)) (pop fields)])
                               ("lean_array_fset" "lean_array_uset")
                               [(release ops world (nth fields (int b))) (assoc fields (int b) c)]
                               "lean_array_fswap" [world (assoc fields (int b) (nth fields (int c))
                                                                                (int c) (nth fields (int b)))])]
          [(replace-fields ops world array node fields) array])
        "lean_mk_array"
        (let [n (size! a) world (if (zero? n) (release ops world b) (retain ops world b (dec n)))]
          ((:allocate ops) world :array 246 (vec (repeat n b))))
        "lean_array_mk"
        (let [fields (loop [list a fields []]
                       (if ((:ref? ops) list)
                         (let [node (node! ops world list :ctor)]
                           (when-not (and (= 1 (:tag node)) (= 2 (count (:fields node))))
                             (fail "Malformed guest list" {:node node}))
                           (recur (second (:fields node)) (conj fields (first (:fields node)))))
                         (if (or (= list 0) (= (:tag list) 0)
                                 (and (native/native-scalar? list) (zero? (native/payload list)))) fields
                           (fail "Malformed guest list terminator" {:value list}))))
              world (reduce #(retain ops %1 %2 1) world fields)
              [world array] ((:allocate ops) world :array 246 fields)]
          [(release ops world a) array])
        "lean_array_to_list"
        (let [fields (:fields (node! ops world a :array))
              [world list] (reduce (fn [[world tail] value]
                                    ((:allocate ops) (retain ops world value 1) :ctor 1 [value tail]))
                                  [world 0] (rseq fields))]
          [(release ops world a) list])
        "lean_st_mk_ref" ((:allocate ops) world :ref 253 [(nth args 2)])
        ("lean_st_ref_get" "lean_st_ref_take")
        (let [ref (nth args 2) node (node! ops world ref :ref)]
          (when-not (= 1 (count (:fields node))) (fail "Read of empty guest reference" {:ref ref}))
          (let [value (first (:fields node))]
            [(if (= symbol "lean_st_ref_get") (retain ops world value 1)
               (replace-fields ops world ref node [])) value]))
        "lean_st_ref_swap"
        (let [ref (nth args 2) value (nth args 3) node (node! ops world ref :ref)]
          (when-not (= 1 (count (:fields node))) (fail "Read of empty guest reference" {:ref ref}))
          ;; Transfer the old field owner to the caller, and the new argument
          ;; owner into the ref. Neither value is retained or released.
          [(replace-fields ops world ref node [value]) (first (:fields node))])
        "lean_st_ref_set"
        (let [ref (nth args 2) value (nth args 3) node (node! ops world ref :ref)
              world (reduce #(release ops %1 %2) world (:fields node))]
          [(replace-fields ops world ref node [value]) 0])))))

#?(:clj
   (do
     ;; Definition-owner baselines, never a snapshot taken by a compiler under
     ;; with-redefs. Foreign classification is checked at its defining owner.
     (def ^:private scalar-arithmetic-generation (Object.))
     (def ^:private scalar-arithmetic-roots [evaluate numeric exact! add negate unsigned pow2 fail])
     (defn scalar-arithmetic-token [] scalar-arithmetic-generation)
     (defn- ordinary-scalar-table? [table]
       (or (= clojure.lang.PersistentArrayMap (class table)) (= clojure.lang.PersistentHashMap (class table))))
     (defn- scalar-route-absent? [table symbol]
       (and (or (ordinary-scalar-table? table) (= clojure.lang.PersistentHashSet (class table)))
            (not (contains? table symbol))))
     (defn- builtin-numeric-route? [symbol operation]
       (and
              (ordinary-scalar-table? supported-symbols)
              (ordinary-scalar-table? (get supported-symbols symbol))
              (= {:arity 2} (get supported-symbols symbol))
              (ordinary-scalar-table? scalar-operations)
              (ordinary-scalar-table? fixed-signed-operations)
              (= operation (get scalar-operations symbol))
              (not (contains? fixed-signed-operations symbol))
              ;; These are the actual earlier evaluate branches. Check relevant
              ;; membership rather than freezing unrelated modules' registries.
              (scalar-route-absent? unsigned-casts symbol)
              (scalar-route-absent? ffi-build-queries symbol)
              (scalar-route-absent? numeric-build-queries symbol)
              (scalar-route-absent? pinned-build symbol)
              (scalar-route-absent? string/supported-symbols symbol)
              (scalar-route-absent? object/supported-symbols symbol)
              (scalar-route-absent? float/supported-symbols symbol)
              (scalar-route-absent? thunk/supported-symbols symbol)
              (scalar-route-absent? thunk/internal-symbols symbol)
              (scalar-route-absent? task/supported-symbols symbol)
              (scalar-route-absent? task/internal-symbols symbol)
              (scalar-route-absent? expr/supported-symbols symbol)
              (scalar-route-absent? sharecommon/supported-symbols symbol)
              (scalar-route-absent? expr-replace/internal-symbols symbol)
              (scalar-route-absent? search/internal-symbols symbol)
              (scalar-route-absent? transform/supported-symbols symbol)
              (scalar-route-absent? bvars/supported-symbols symbol)
              (scalar-route-absent? mvars/supported-symbols symbol)
              (scalar-route-absent? mvars/internal-symbols symbol)
              (scalar-route-absent? expr-mvars/supported-symbols symbol)
              (scalar-route-absent? expr-mvars/internal-symbols symbol)
              (scalar-route-absent? io/supported-symbols symbol)
              (scalar-route-absent? sync/supported-symbols symbol)
              (scalar-route-absent? heartbeat/supported-symbols symbol) ))
     (defn builtin-scalar-arithmetic? [symbol operation]
       (let [[e n x a neg u p f] scalar-arithmetic-roots]
         (and (contains? #{"lean_uint64_add" "lean_uint64_sub" "lean_usize_add" "lean_usize_sub" "lean_uint64_dec_eq" "lean_usize_dec_eq"} symbol)
              (identical? e evaluate) (identical? n numeric) (identical? x exact!)
              (identical? a add) (identical? neg negate) (identical? u unsigned)
              (identical? p pow2) (identical? f fail)
              (scalar/builtin-scalar-integer?)
              (builtin-numeric-route? symbol operation))))))

#?(:clj
   (do
     (def ^:private nat-arithmetic-generation (Object.))
     (def ^:private nat-arithmetic-roots [evaluate numeric nat! exact! add negate fail])
     (defn nat-arithmetic-token [] nat-arithmetic-generation)
     (defn builtin-nat-arithmetic?
       "Operation is the exact runtime operation from the sealed ABI registry."
       [symbol operation]
       (let [[e n nat exact a neg f] nat-arithmetic-roots]
         (and (contains? #{"lean_nat_add" "lean_nat_sub" "lean_nat_dec_eq"} symbol)
              (identical? e evaluate) (identical? n numeric) (identical? nat nat!)
              (identical? exact exact!) (identical? a add) (identical? neg negate)
              (identical? f fail) (native/builtin-native-number?)
              (builtin-numeric-route? symbol operation))))))
