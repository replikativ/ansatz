(ns prototype.runtime-integer-test
  "Pinned native oracle vectors; fixture integers are decimal strings.
   Node supports only exact Number inputs/intermediates/results, and must reject
   the other vectors explicitly rather than approximate full-width arithmetic."
  (:require [prototype.runtime-prim :as runtime]
            #?(:clj [prototype.runtime-abi :as abi])
            #?(:clj [prototype.machine :as m])
            #?(:clj [prototype.raw-interop :as raw])
            #?(:clj [clojure.data.json :as json])
            [clojure.string :as str]
            #?(:clj [clojure.test :refer [deftest is testing]]
               :cljs [cljs.test :refer-macros [deftest is testing]])))

(defn vectors []
  (let [text #?(:clj (slurp "fixtures/runtime-integers.jsonl")
                :cljs (.readFileSync (js/require "fs") "fixtures/runtime-integers.jsonl" "utf8"))]
    (mapv #?(:clj #(json/read-str % :key-fn keyword)
             :cljs #(js->clj (js/JSON.parse %) :keywordize-keys true))
          (remove str/blank? (str/split-lines text)))))

(defn argument [value]
  (if (nil? value) ::erased #?(:clj (bigint value) :cljs (js/Number value))))

(deftest native-integer-vectors-match-or-reject-inexact-host-values
  (let [rows (vectors) world {:test :unchanged}]
    (is (> (count rows) 250))
    (doseq [{:keys [symbol args expected jsExact]} rows]
      (testing (str symbol " " args)
        (let [args (mapv argument args)]
          #?(:clj (let [[actual-world result] (runtime/evaluate {} world symbol args)]
                    (is (= world actual-world))
                    (is (= expected (str result))))
             :cljs (if jsExact
                     (let [[actual-world result] (runtime/evaluate {} world symbol args)]
                       (is (= world actual-world))
                       (is (= expected (str result))))
                     (is (thrown-with-msg? js/Error #"exact|unsigned range"
                           (runtime/evaluate {} world symbol args))))))))))

(deftest uint-proof-and-no-proof-abis-are-distinct-and-supported
  (doseq [stem ["uint8" "uint16" "uint32" "uint64" "usize"]]
    (let [symbol (str "lean_" stem "_of_nat")]
      (is (= [nil 42] (runtime/evaluate {} nil symbol [42])))
      (is (= [nil 42] (runtime/evaluate {} nil symbol [42 ::erased])))
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"arity"
            (runtime/evaluate {} nil symbol [42 ::erased ::extra]))))))

(deftest pinned-unsigned-casts-and-consuming-nat-conversions-are-covered
  ;; All twenty cast names occur literally in pinned lean.h:2043–2205.
  ;; Unlike *_of_nat, *_of_nat_mk owns its Nat (lean_dec in the C helper).
  ;; Guest Nats are immediate host integers, with no guest heap reference to drop.
  (let [rows (vectors)
        names (set (map :symbol rows))
        casts (set (for [source ["uint8" "uint16" "uint32" "uint64" "usize"]
                         target ["uint8" "uint16" "uint32" "uint64" "usize"]
                         :when (not= source target)]
                     (str "lean_" source "_to_" target)))]
    (is (= (into casts (map #(str "lean_bool_to_" %) ["uint8" "uint16" "uint32" "uint64" "usize"
                                                       "int8" "int16" "int32" "int64" "isize"]))
           (set (keys runtime/unsigned-casts))))
    (doseq [target ["uint8" "uint16" "uint32" "uint64" "usize" "int8" "int16" "int32" "int64" "isize"]
            value [0 1]]
      (is (= [nil value] (runtime/evaluate {} nil (str "lean_bool_to_" target) [value]))))
    (is (= 20 (count casts)))
    (doseq [symbol casts]
      (is (contains? names symbol))
      (is (= {:arity 1} (get runtime/supported-symbols symbol))))
    (doseq [stem ["uint8" "uint16" "uint32" "uint64" "usize"]]
      (let [symbol (str "lean_" stem "_of_nat_mk")]
        (is (contains? names symbol))
        (is (= [nil 42] (runtime/evaluate {} nil symbol [42])))
        (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"arity"
              (runtime/evaluate {} nil symbol [42 ::erased])))))
    (doseq [suffix ["add" "sub" "mul" "land" "lor" "shift_left"]]
      (is (contains? names (str "lean_uint64_" suffix))))))

(deftest nat-shift-allocation-limit-is-explicit-and-zero-short-circuits
  ;; Nonzero shifts this large would allocate hundreds of MiB; do not attempt
  ;; them in the oracle. The prototype intentionally limits the JVM shift count.
  (is (= [nil 0] (runtime/evaluate {} nil "lean_nat_shiftl" [0 2147483648])))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"allocation"
        (runtime/evaluate {} nil "lean_nat_shiftl" [1 2147483648])))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Expected Nat"
        (runtime/evaluate {} nil "lean_nat_shiftl" [1 -1])))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Unsupported runtime"
        (runtime/evaluate {} nil "lean_integer_made_up" [1]))))

(deftest nat-gcd-preserves-borrowed-values-and-exact-integer-domain
  ;; Pinned object.cpp delegates all scalar/mpz combinations to nonnegative gcd.
  (doseq [[left right expected] [[0 0 0] [0 42 42] [42 0 42] [1 1000000000 1]
                                [48 18 6] [1071 462 21] [9007199254740990 2 2]]]
    (let [world {:unchanged true}]
      (is (= [world expected] (runtime/evaluate {} world "lean_nat_gcd" [left right])))
      (is (= [world expected] (runtime/evaluate {} world "lean_nat_gcd" [right left])))))
  #?(:clj (is (= [nil 18446744073709551616N]
                 (runtime/evaluate {} nil "lean_nat_gcd" [36893488147419103232N 55340232221128654848N])))
     :cljs (is (thrown-with-msg? js/Error #"exact host range"
                 (runtime/evaluate {} nil "lean_nat_gcd" [9007199254740992 2]))))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Expected Nat"
        (runtime/evaluate {} nil "lean_nat_gcd" [-1 2]))))

(def native-division-cases
  [[-17 -7 2 -3 3 4]
   [-17 -3 5 -2 6 1]
   [-17 -1 17 0 17 0]
   [-17 0 0 -17 0 -17]
   [-17 1 -17 0 -17 0]
   [-17 3 -5 -2 -6 1]
   [-17 7 -2 -3 -3 4]
   [-12 -7 1 -5 2 2]
   [-12 -3 4 0 4 0]
   [-12 -1 12 0 12 0]
   [-12 0 0 -12 0 -12]
   [-12 1 -12 0 -12 0]
   [-12 3 -4 0 -4 0]
   [-12 7 -1 -5 -2 2]
   [-1 -7 0 -1 1 6]
   [-1 -3 0 -1 1 2]
   [-1 -1 1 0 1 0]
   [-1 0 0 -1 0 -1]
   [-1 1 -1 0 -1 0]
   [-1 3 0 -1 -1 2]
   [-1 7 0 -1 -1 6]
   [0 -7 0 0 0 0]
   [0 -3 0 0 0 0]
   [0 -1 0 0 0 0]
   [0 0 0 0 0 0]
   [0 1 0 0 0 0]
   [0 3 0 0 0 0]
   [0 7 0 0 0 0]
   [1 -7 0 1 0 1]
   [1 -3 0 1 0 1]
   [1 -1 -1 0 -1 0]
   [1 0 0 1 0 1]
   [1 1 1 0 1 0]
   [1 3 0 1 0 1]
   [1 7 0 1 0 1]
   [12 -7 -1 5 -1 5]
   [12 -3 -4 0 -4 0]
   [12 -1 -12 0 -12 0]
   [12 0 0 12 0 12]
   [12 1 12 0 12 0]
   [12 3 4 0 4 0]
   [12 7 1 5 1 5]
   [17 -7 -2 3 -2 3]
   [17 -3 -5 2 -5 2]
   [17 -1 -17 0 -17 0]
   [17 0 0 17 0 17]
   [17 1 17 0 17 0]
   [17 3 5 2 5 2]
   [17 7 2 3 2 3]])

(deftest signed-division-families-match-pinned-native-oracle
  ;; Pinned Lean4.33.1 native Init: all sign combinations, including divisor0.
  (doseq [[a b trunc-q trunc-r euclidean-q euclidean-r] native-division-cases
          [symbol expected] [["lean_int_div" trunc-q] ["lean_int_mod" trunc-r]
                             ["lean_int_ediv" euclidean-q] ["lean_int_emod" euclidean-r]]]
    (let [world {:unchanged true}]
      (is (= [world expected] (runtime/evaluate {} world symbol [a b])))))
  ;; Euclidean remainder is nonnegative; truncating remainder follows numerator.
  (is (= [nil -1] (runtime/evaluate {} nil "lean_int_mod" [-10 -3])))
  (is (= [nil 2] (runtime/evaluate {} nil "lean_int_emod" [-10 -3]))))

(deftest exact-division-keeps-erased-proof-position-and-validates-its-precondition
  (doseq [[symbol a b expected] [["lean_int_div_exact" 1 1 1]
                                ["lean_int_div_exact" -15 5 -3]
                                ["lean_int_div_exact" 21 -3 -7]
                                ["lean_int_div_exact" -21 -3 7]
                                ["lean_int_div_exact" 0 0 0]
                                ["lean_nat_div_exact" 21 3 7]
                                ["lean_nat_div_exact" 0 22 0]
                                ["lean_nat_div_exact" 0 0 0]]]
    (is (= [nil expected] (runtime/evaluate {} nil symbol [a b ::erased]))))
  (doseq [symbol ["lean_nat_div_exact" "lean_int_div_exact"]]
    (is (= {:arity 3} (get runtime/supported-symbols symbol)))
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"arity"
          (runtime/evaluate {} nil symbol [1 1])))
    (doseq [[a b] [[7 3] [1 0]]]
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"divisible pair"
            (runtime/evaluate {} nil symbol [a b ::erased])))))
  (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"Expected Nat"
        (runtime/evaluate {} nil "lean_nat_div_exact" [-6 3 ::erased]))))

(deftest division-preserves-full-jvm-integers-or-rejects-inexact-node-carriers
  #?(:clj
     (do
       ;; Primitive long division would wrap this one result.
       (doseq [symbol ["lean_int_div" "lean_int_ediv"]]
         (is (= [nil 9223372036854775808N] (runtime/evaluate {} nil symbol [Long/MIN_VALUE -1]))))
       (is (= [nil 9223372036854775808N]
              (runtime/evaluate {} nil "lean_int_div_exact" [Long/MIN_VALUE -1 ::erased])))
       (let [n -340282366920938463463374607431768211456N]
         (is (= [nil -113427455640312821154458202477256070486N]
                (runtime/evaluate {} nil "lean_int_ediv" [n 3])))
         (is (= [nil 2] (runtime/evaluate {} nil "lean_int_emod" [n 3])))
         (is (= [nil -113427455640312821154458202477256070485N]
                (runtime/evaluate {} nil "lean_int_div" [n 3])))
         (is (= [nil -1] (runtime/evaluate {} nil "lean_int_mod" [n 3])))
         (is (= [nil -85070591730234615865843651857942052864N]
                (runtime/evaluate {} nil "lean_int_div_exact" [n 4 ::erased])))))
     :cljs
     (doseq [symbol ["lean_int_div" "lean_int_mod" "lean_int_ediv" "lean_int_emod"
                    "lean_int_div_exact" "lean_nat_div_exact"]]
       (is (thrown-with-msg? js/Error #"exact host range"
             (runtime/evaluate {} nil symbol
               (if (.endsWith symbol "_exact") [9007199254740992 2 ::erased] [9007199254740992 2])))))))

(deftest uint32-add-wraps-exactly-at-native-width
  ;; Pinned lean.h:2092 uses uint32_t addition, modulo 2^32.
  (doseq [[left right expected] [[0 1 1] [4294967295 1 0]
                                [2147483648 2147483648 0]
                                [4294967295 4294967295 4294967294]]]
    (is (= [nil expected] (runtime/evaluate {} nil "lean_uint32_add" [left right]))))
  (doseq [invalid [-1 4294967296]]
    (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"unsigned range"
          (runtime/evaluate {} nil "lean_uint32_add" [invalid 1])))))

#?(:clj
   (deftest uint32-less-than-native-boundaries-through-actual-abi
     (let [name ["str" ["str" ["anonymous"] "UInt32"] "decLt"]
           row {:kind "decl" :name name :ir {:extern {:f name :type "uint8"
                 :xs [{:x {:idx 1} :ty "uint32" :borrow false}
                      {:x {:idx 2} :ty "uint32" :borrow false}]
                 :ext {:entries [{:standard {:backend ["str" ["anonymous"] "all"]
                                            :fn "lean_uint32_dec_lt"}}]}}}}
           [target function] (abi/lower row)
           cases (filter #(= "lean_uint32_dec_lt" (:symbol %)) (vectors))]
       (is (= 49 (count cases)))
       (is (= "lean_uint32_dec_lt" (:runtime-extern function)))
       (doseq [backend [:reference :mutable :jvm]]
         (let [functions {target function} session (raw/open-functions functions {} {:backend backend})
               world (m/world functions)]
           (doseq [{:keys [args expected]} cases]
             (let [{:keys [state value]} (raw/call session world target (mapv argument args))]
               (is (= expected (str value)) [backend args])
               (is (= (:heap world) (:heap state)))))))
       (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unrecognized raw runtime ownership/type signature"
             (abi/lower (assoc-in row [:ir :extern :xs 0 :borrow] true)))))))
