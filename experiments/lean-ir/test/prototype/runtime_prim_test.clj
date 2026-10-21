(ns prototype.runtime-prim-test
  (:require [clojure.test :refer [deftest is testing]]
            [prototype.machine :as m]
            [prototype.runtime-prim :as prim]))

(def ops {:ref? m/ref? :node m/node :allocate m/allocate :retain m/retain :release m/release
          :replace-node (fn [s r n] (assoc-in s [:heap (:id r)] n))})
(defn evaluate [s symbol args] (prim/evaluate ops s symbol args))
(defn result [symbol args] (second (evaluate (m/world {}) symbol args)))

(deftest initialization-bit-comes-from-guest-world
  (let [ops (assoc ops :initializing? :initializing?)
        initial (assoc (m/world {}) :initializing? true)
        running (assoc initial :initializing? false)]
    (is (= [initial 1] (prim/evaluate ops initial "lean_io_initializing" [m/erased])))
    (is (= [running 0] (prim/evaluate ops running "lean_io_initializing" [m/erased])))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Missing guest initialization context"
          (evaluate initial "lean_io_initializing" [m/erased])))))

(deftest arithmetic-boundaries
  (is (= 0 (result "lean_nat_sub" [2 3])))
  (is (= 0 (result "lean_nat_div" [7 0])))
  (is (= 7 (result "lean_nat_mod" [7 0])))
  (is (= 1267650600228229401496703205376N (result "lean_nat_pow" [2 100])))
  (is (= 0 (result "lean_nat_shiftr" [7 1267650600228229401496703205376N])))
  (is (= 1 (result "lean_nat_dec_lt" [1 2])))
  (is (= -9 (result "lean_int_add" [-12 3])))
  (is (= 12 (result "lean_nat_abs" [-12])))
  (is (= 9223372036854775808N (result "lean_int_neg" [Long/MIN_VALUE])))
  (is (= 9223372036854775808N (result "lean_nat_abs" [Long/MIN_VALUE])))
  (is (= -18446744073709551616N
         (result "lean_int_add" [Long/MIN_VALUE Long/MIN_VALUE])))
  (is (= 0 (result "lean_usize_add" [18446744073709551615N 1])))
  (is (= 18446744073709551615N (result "lean_usize_sub" [0 1])))
  (is (= 1 (result "lean_uint64_shift_right" [8 67])))
  (is (= 0 (result "lean_uint64_xor" [18446744073709551615N 18446744073709551615N])))
  (is (= 255 (result "lean_uint32_to_uint8" [4294967295])))
  (is (= 1 (result "lean_uint64_of_nat" [18446744073709551617N m/erased])))
  (is (= 1 (result "lean_uint64_of_nat" [18446744073709551617N])))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Expected Nat" (result "lean_nat_add" [-1 1])))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"arity" (result "lean_nat_add" [1])))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unsupported runtime" (result "lean_missing_primitive" ["x"]))))

(deftest owning-and-borrowed-array-reads
  (let [[s value] (m/allocate (m/world {}) :ctor 1 [42])
        [s array] (m/allocate s :array 246 [value])
        [borrowed actual] (evaluate s "lean_array_uget_borrowed" [m/erased array 0 m/erased])
        [owned actual-owned] (evaluate s "lean_array_fget" [m/erased array 0 m/erased])]
    (is (= value actual actual-owned))
    (is (= 1 (:rc (m/node borrowed value))))
    (is (= 2 (:rc (m/node owned value))))
    (is (= 64 (result "lean_system_platform_nbits" [0])))))

(deftest array-updates-follow-ownership
  (let [[s old] (m/allocate (m/world {}) :ctor 1 [10])
        [s value] (m/allocate s :ctor 1 [20])
        [s array] (m/allocate s :array 246 [old])
        [unique updated] (evaluate s "lean_array_uset" [m/erased array 0 value m/erased])
        shared (m/retain s array 1)
        [copied copy] (evaluate shared "lean_array_uset" [m/erased array 0 value m/erased])
        persistent (assoc-in s [:heap (:id array) :rc] 0)
        [forked fork] (evaluate persistent "lean_array_push" [m/erased array value])]
    (is (= array updated))
    (is (not (contains? (:heap unique) (:id old))))
    (is (= [value] (:fields (m/node unique array))))
    (is (not= array copy))
    (is (= [old] (:fields (m/node copied array))))
    (is (= [value] (:fields (m/node copied copy))))
    (is (= 1 (:rc (m/node copied old))))
    (is (= 1 (:rc (m/node copied array))))
    (is (not= array fork))
    (is (= [old] (:fields (m/node forked array))))
    (is (= [old value] (:fields (m/node forked fork))))
    (is (= 2 (:rc (m/node forked old))))
    (is (= s (assoc-in persistent [:heap (:id array) :rc] 1)))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"out of bounds"
          (evaluate s "lean_array_uset" [m/erased array 1 value m/erased])))))

(deftest array-pop-swap-replication-and-list-transfer
  (let [[s x] (m/allocate (m/world {}) :ctor 1 [10])
        [s array] (evaluate s "lean_mk_array" [m/erased 3 x])
        [s popped] (evaluate s "lean_array_pop" [m/erased array])
        [s list] (evaluate s "lean_array_to_list" [m/erased popped])
        [s roundtrip] (evaluate s "lean_array_mk" [m/erased list])]
    (is (= [x x] (:fields (m/node s roundtrip))))
    (is (= 2 (:rc (m/node s x))))
    (is (not (contains? (:heap s) (:id array))))
    (let [[s empty] (evaluate s "lean_mk_empty_array_with_capacity" [m/erased 12])]
      (is (= [s empty] (evaluate s "lean_array_pop" [m/erased empty])))))
  (let [[s array] (m/allocate (m/world {}) :array 246 [10 20])
        [s swapped] (evaluate s "lean_array_fswap" [m/erased array 0 1 m/erased m/erased])]
    (is (= array swapped))
    (is (= [20 10] (:fields (m/node s array))))))

(deftest refs-transfer-values-and-preserve-snapshot-isolation
  (let [[s value] (m/allocate (m/world {}) :ctor 1 [42])
        [s ref] (evaluate s "lean_st_mk_ref" [m/erased m/erased value m/erased])
        [read actual] (evaluate s "lean_st_ref_get" [m/erased m/erased ref m/erased])
        [taken actual-taken] (evaluate s "lean_st_ref_take" [m/erased m/erased ref m/erased])
        persistent (assoc-in s [:heap (:id ref) :rc] 0)
        [child replacement] (m/allocate persistent :ctor 2 [43])
        [child unit] (evaluate child "lean_st_ref_set" [m/erased m/erased ref replacement m/erased])]
    (is (= value actual actual-taken))
    (is (= 2 (:rc (m/node read value))))
    (is (= 1 (:rc (m/node taken value))))
    (is (empty? (:fields (m/node taken ref))))
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"empty guest reference"
          (evaluate taken "lean_st_ref_get" [m/erased m/erased ref m/erased])))
    (is (= 0 unit))
    (is (= 0 (:rc (m/node child ref))))
    (is (= 1 (:rc (m/node child replacement))) "new persistent-ref content is collectable")
    (is (= [value] (:fields (m/node persistent ref))))
    (is (= [replacement] (:fields (m/node child ref))))
    (is (not (contains? (:heap child) (:id value))))))

(deftest ref-replacement-preserves-count-changes-through-cycles
  (let [[s ref] (evaluate (m/world {}) "lean_st_mk_ref" [m/erased m/erased 0 m/erased])
        s (m/retain s ref 1)
        [s _] (evaluate s "lean_st_ref_set" [m/erased m/erased ref ref m/erased])
        [s _] (evaluate s "lean_st_ref_set" [m/erased m/erased ref 42 m/erased])]
    (is (= 1 (:rc (m/node s ref))))
    (is (= [42] (:fields (m/node s ref))))))

(deftest unsigned-nat-conversion-proof-arguments-and-wraparound
  (doseq [[symbol modulus] [["lean_uint8_of_nat" 256] ["lean_uint16_of_nat" 65536]
                            ["lean_uint32_of_nat" 4294967296N]
                            ["lean_uint64_of_nat" 18446744073709551616N]
                            ["lean_usize_of_nat" 18446744073709551616N]]
          value [0 1 (dec modulus) modulus (inc modulus) 1267650600228229401496703205377N]
          args [[value] [value m/erased]]]
    (is (= (mod value modulus) (result symbol args))))
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Expected Nat"
                       (result "lean_uint8_of_nat" [-1]))))

(deftest metadata-refers-to-the-pinned-guest-build
  (doseq [[symbol expected] [["lean_version_get_major" 4] ["lean_version_get_minor" 33]
                             ["lean_version_get_patch" 1] ["lean_version_get_is_release" 1]
                             ["lean_version_get_special_desc" ""]
                             ["lean_get_githash" "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"]]]
    (let [world (m/world {})]
      (is (= [world expected] (evaluate world symbol [(m/->Tag 0)]))))))

(deftest signed-fixed-width-operations-use-unsigned-carriers
  (doseq [[prefix modulus] [["int8" 256] ["int16" 65536] ["int32" 4294967296N]
                             ["int64" 18446744073709551616N] ["isize" 18446744073709551616N]]]
    (let [call (fn [suffix args] (result (str "lean_" prefix "_" suffix) args))]
      (is (= 1 (call "of_nat" [(inc modulus)])))
      (is (= (dec modulus) (call "neg" [1])))
      (is (= (quot modulus 2) (call "neg" [(quot modulus 2)])))
      (is (= 0 (call "add" [(dec modulus) 1])))
      (is (= (dec modulus) (call "sub" [0 1])))
      (is (= 2 (call "mul" [(dec modulus) (- modulus 2)])))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Expected Nat" (call "of_nat" [-1]))))))

(deftest reference-swap-transfers-owners-without-copying
  (doseq [persistent? [false true]]
    (let [[world old] (m/allocate (m/world {}) :ctor 0 [])
          [world ref] (m/allocate world :ref 253 [old])
          world (if persistent? (m/mark-persistent world ref) world)
          [world new] (m/allocate world :ctor 1 [])
          [updated returned] (evaluate world "lean_st_ref_swap" [m/erased m/erased ref new m/erased])]
      (is (= old returned))
      (is (= [new] (:fields (m/node updated ref))))
      (is (= [old] (:fields (m/node world ref))))
      (is (= (:rc (m/node world old)) (:rc (m/node updated old))))
      (is (= 1 (:rc (m/node updated new))))
      (is (= (:rc (m/node world ref)) (:rc (m/node updated ref))))))
  (let [[world ref] (m/allocate (m/world {}) :ref 253 [])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"empty guest reference"
          (evaluate world "lean_st_ref_swap" [m/erased m/erased ref 1 m/erased])))))
