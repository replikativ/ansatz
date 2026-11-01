(ns prototype.native-runtime-test
  "Native tagged words stay untyped until a pinned runtime ABI supplies context."
  (:require [prototype.native-scalar :as native]
            [prototype.scalar :as scalar]
            [prototype.machine :as m]
            [prototype.runtime-prim :as runtime]
            #?(:clj [prototype.mutable :as u])
            #?(:clj [prototype.block-compile :as blocks])
            #?(:clj [prototype.lazy-runtime :as lazy])
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(def ops {:ref? m/ref? :node m/node :allocate m/allocate :retain m/retain :release m/release
          :replace-node (fn [s r n] (assoc-in s [:heap (:id r)] n))})
(defn evaluate [world symbol args] (runtime/evaluate ops world symbol args))
(defn mpz [world integer]
  (let [[world r] (m/allocate world :mpz 250 [])]
    [(assoc-in world [:heap (:id r) :integer] integer) r]))

(deftest one-native-word-has-distinct-nat-int-and-unboxed-contexts
  ;; lean.h:1722–1735: small Int casts unsigned payload to signed C int.
  (let [raw (native/native-scalar 4294967295) world (m/world {})]
    (is (= [world 4294967295] (evaluate world "lean_nat_add" [raw 0])))
    (is (= [world -1] (evaluate world "lean_int_add" [raw 0])))
    (is (= [world 1] (evaluate world "lean_nat_abs" [raw])))
    (is (= [world 255] (evaluate world "lean_uint8_of_nat" [raw])))
    (is (= [world 255] (evaluate world "lean_int8_of_int" [raw])))
    (is (= 255 (scalar/integer! "uint8" (native/native-scalar 511))))
    (is (= 65535 (scalar/integer! "uint16" raw)))
    (is (= 255 (m/unbox-value world "uint8" raw)))
    (is (= [world 255] (m/box-value world "uint8" raw)))
    (let [layout {:objects 0 :usize 0 :ssize 1}
          slot {:index 0 :offset 0 :type "uint8" :region :scalar}]
      (is (= {0 255} (scalar/write-bytes layout {} slot raw))))
    (is (= 4294967295 (m/tag world raw)))
    (is (= 0 (m/tag world (native/native-scalar 4294967296))))
    (is (= 8589934591 (m/pointer-address world raw)))
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                 (scalar/integer! "uint8" 511)))
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                 (m/unbox-value world "uint64" raw)))))

(deftest mpz-borrowed-arithmetic-and-owned-conversions
  (let [[world p] (mpz (m/world {}) 4294967296)
        [world n] (mpz world -4294967296)]
    (doseq [[symbol args expected]
            [["lean_nat_add" [p 1] 4294967297]
             ["lean_int_sub" [n p] -8589934592]
             ["lean_int_dec_lt" [n p] 1]
             ["lean_nat_abs" [n] 4294967296]
             ["lean_uint8_of_nat" [p] 0]]]
      (is (= [world expected] (evaluate world symbol args))))
    (is (= [world p] (evaluate world "lean_nat_to_int" [p])))
    (let [[after result] (evaluate world "lean_nat_abs" [p])]
      (is (= 4294967296 result))
      (is (= 1 (:rc (m/node after p))))
      (is (= 1 (:rc (m/node world p)))))
    (let [[after result] (evaluate world "lean_uint8_of_nat_mk" [p])]
      (is (= 0 result))
      (is (not (contains? (:heap after) (:id p))))
      (is (= 1 (:rc (m/node world p)))))
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                 (evaluate world "lean_nat_add" [n 0])))
    (is (not (m/erased-callee? p)))
    (let [persistent (m/mark-persistent world p)]
      (is (= [persistent 4294967296] (evaluate persistent "lean_nat_abs" [p])))
      (is (= [persistent 0] (evaluate persistent "lean_uint8_of_nat_mk" [p]))))))

(deftest native-full-width-and-malformed-number-boundaries
  (let [world (m/world {})]
    #?(:clj
       (is (= 18446744073709551615N
              (m/pointer-address world (native/native-scalar 9223372036854775807N))))
       :cljs
       (is (thrown-with-msg? js/Error #"exact JS profile"
             (m/pointer-address world (native/native-scalar 9007199254740991)))))
    (let [[world invalid] (m/allocate world :ctor 0 [])]
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"MPZ"
            (evaluate world "lean_nat_add" [invalid 0]))))
    (let [[world malformed] (mpz world 7)
          world (assoc-in world [:heap (:id malformed) :fields] [0])]
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"MPZ"
            (evaluate world "lean_int_add" [malformed 0]))))))

(deftest array-index-context-and-erased-list-terminator
  (let [zero (native/native-scalar 0) one (native/native-scalar 1)
        raw (native/native-scalar 4294967295)
        [world index] (mpz (m/world {}) 4294967296)
        [world array] (m/allocate world :array 246 [zero raw])]
    (is (= [world raw] (evaluate world "lean_array_fget_borrowed" [m/erased array one m/erased])))
    (is (= [world raw] (evaluate world "lean_array_uget_borrowed" [m/erased array one m/erased])))
    (let [[world list] (m/allocate world :ctor 1 [raw zero])
          [after result] (evaluate world "lean_array_mk" [m/erased list])]
      (is (= [raw] (:fields (m/node after result))))
      (is (not (contains? (:heap after) (:id list)))))
    (let [[world bytes] (evaluate world "lean_byte_array_mk" [array])]
      (is (= [0 255] (:bytes (m/node world bytes))))
      (is (= [world 0] (evaluate world "lean_byte_array_get" [bytes index])))
      (is (= [world 255] (evaluate world "lean_byte_array_uget" [bytes one m/erased]))))))

(deftest names-have-contextual-terminators-and-nat-components
  (let [zero (native/native-scalar 0)
        raw (native/native-scalar 4294967295)
        [world number] (mpz (m/world {}) 4294967295)
        [world a] (m/allocate world :ctor 2 [zero raw])
        [world b] (m/allocate world :ctor 2 [0 number])]
    (is (= [world 1] (evaluate world "lean_name_eq" [a b])))
    (is (= [world 1] (evaluate world "lean_name_eq" [zero (m/->Tag 0)])))
    (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
                 (evaluate world "lean_name_eq" [raw zero])))))

(deftest native-name-string-components-preserve-borrowed-heap
  (let [[world string] (m/allocate (m/world {}) :string 249 [])
        world (assoc-in world [:heap (:id string) :text] "é😀")
        [world a] (m/allocate world :ctor 1 [(native/native-scalar 0) string])
        [world b] (m/allocate world :ctor 1 [0 "é😀"])]
    (is (= [world 1] (evaluate world "lean_name_eq" [a b])))
    (is (= 1 (:rc (m/node world string))))))

(deftest persistent-native-leaves-and-erased-callee-ownership
  (let [raw (native/native-scalar 4294967295)
        [world owned] (m/resource (m/world {}) :argument)
        call-world (assoc world :locals {0 raw})
        result (m/apply-target call-world [:closure [:var 0]] [owned])]
    (is (= raw (:result result)))
    (is (= [[:released :argument]] (get-in result [:state :events]))))
  (doseq [[kind tag] [[:mpz 250] [:string 249] [:scalar-array 248]]]
    (let [[world leaf] (m/allocate (m/world {}) kind tag [])
          world (m/mark-persistent world leaf)]
      (is (= 0 (:rc (m/node world leaf))))
      (is (= world (m/release world leaf 1))))))

#?(:clj
   (deftest mutable-adapter-has-the-same-context-and-ownership
     (let [[world p] (mpz (m/world {}) 4294967296)
           machine (u/thaw world)]
       (is (= 4294967297 (u/runtime-value! machine "lean_nat_add" [p (native/native-scalar 1)])))
       (is (= -1 (u/runtime-value! machine "lean_int_add" [(native/native-scalar 4294967295) 0])))
       (is (= 0 (u/tag-of machine (native/native-scalar 4294967296))))
       (is (= 250 (u/tag-of machine p)))
       (is (= 0 (u/runtime-value! machine "lean_uint8_of_nat_mk" [p])))
       (is (not (contains? (:heap (u/freeze machine)) (:id p)))))))

#?(:clj
   (deftest native-carriers-run-identically-at-every-fuel-boundary
     (let [functions
           {:arith {:params [0 1]
                    :body [:let 2 [:runtime "lean_int_add" [[:var 0] [:var 1]]]
                           [:let 3 [:box "uint8" [:var 0]] [:return [:var 2]]]]}
            :tag {:params [0] :body [:case [:var 0] [[0 [:return [:imm 7]]] [1 [:return [:imm 8]]]]]}
            :apply {:params [0 1] :body [:call 2 [:closure [:var 0]] [[:var 1]] [:return [:var 2]]]}}
           eager (blocks/compile-program functions nil {:lexical-joins true})
           delayed (lazy/open-program functions)
           [world argument] (m/resource (m/world functions) :owned)
           [world mpz] (mpz world -4294967296)
           initial [(m/start world :arith [(native/native-scalar 4294967295) mpz])
                    (m/start world :tag [(native/native-scalar 4294967296)])
                    (m/start world :apply [(native/native-scalar 0) argument])]]
       (doseq [initial initial
               fuel (range 7)]
         (let [expected (m/run initial fuel)]
           (is (= expected (u/freeze (u/run! (u/thaw initial) fuel))))
           (is (= expected (u/freeze (blocks/run! eager (u/thaw initial) fuel))))
           (is (= expected (u/freeze (lazy/run! delayed (u/thaw initial) fuel)))))))))

#?(:cljs (do (defn -main [] (cljs.test/run-tests 'prototype.native-runtime-test))
             (set! *main-cli-fn* -main)))
