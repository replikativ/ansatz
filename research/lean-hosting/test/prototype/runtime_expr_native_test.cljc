(ns prototype.runtime-expr-native-test
  "Imported ModuleData scalars are interpreted at Expr/Level field types."
  (:require [prototype.runtime-expr :as runtime]
            #?(:cljs [prototype.runtime-io-test])
            [prototype.native-scalar :as native]
            [prototype.machine :as m]
            #?(:clj [prototype.mutable :as u])
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))

(def ops {:ref? m/ref? :node m/node})
(def zero (native/native-scalar 0))
(defn mpz [world number]
  (let [[world value] (m/allocate world :mpz 250 [])]
    [(assoc-in world [:heap (:id value) :integer] number) value]))
(defn cached [world tag fields]
  (let [[world value] (m/allocate world :ctor tag fields)]
    [(update-in world [:heap (:id value)] assoc
                :layout {:objects (count fields) :usize 0 :ssize 8}
                :scalar-bytes (zipmap (range (* 8 (count fields)) (+ (* 8 (count fields)) 8)) (repeat 0))) value]))
(defn compare-exprs [world a b expected]
  (doseq [symbol ["lean_expr_eqv" "lean_expr_equal"]]
    (is (= [world expected] (runtime/evaluate ops world symbol [a b])))))
(defn metadata [world name value child]
  (let [[world pair] (m/allocate world :ctor 0 [name value])
        [world entries] (m/allocate world :ctor 1 [pair zero])]
    (cached world 10 [entries child])))

(deftest native-zero-level-list-and-bvar-contexts
  (let [world (m/world {})
        raw (native/native-scalar 4294967295)
        [world a] (cached world 0 [raw])
        [world b] (cached world 0 [4294967295])
        [world c] (cached world 0 [0])
        [world sa] (cached world 3 [zero])
        [world sb] (cached world 3 [(m/->Tag 0)])
        [world name] (m/allocate world :ctor 2 [zero (native/native-scalar 1)])
        [world ca] (cached world 4 [name zero])
        [world cb] (cached world 4 [name 0])]
    (is (= [world 1] (runtime/evaluate ops world "lean_level_eq" [zero 0])))
    (compare-exprs world a b 1)
    (compare-exprs world a c 0)
    (compare-exprs world sa sb 1)
    (compare-exprs world ca cb 1)))

(deftest literal-and-metadata-numbers-borrow-native-objects
  (let [world (m/world {})
        [world name] (m/allocate world :ctor 2 [zero (native/native-scalar 1)])
        [world child] (cached world 3 [zero])
        [world number] (mpz world 1099511627776)
        [world negative] (mpz world -1099511627776)
        [world string] (m/allocate world :string 249 [])
        world (assoc-in world [:heap (:id string) :text] "é😀")]
    (doseq [[tag native-value host-value]
            [[3 (native/native-scalar 4294967295) 4294967295]
             [4 (native/native-scalar 4294967295) -1]
             [3 number 1099511627776]
             [4 negative -1099511627776]
             [0 string "é😀"]]]
      (let [[world a] (m/allocate world :ctor tag [native-value])
            [world b] (m/allocate world :ctor tag [host-value])
            [world left] (metadata world name a child)
            [world right] (metadata world name b child)]
        (compare-exprs world left right 1)
        (is (= 1 (:rc (m/node world number))))
        (is (= 1 (:rc (m/node world negative))))))
    (doseq [[tag native-value host-value] [[0 number 1099511627776] [1 string "é😀"]]]
      (let [[world a] (m/allocate world :ctor tag [native-value])
            [world b] (m/allocate world :ctor tag [host-value])
            [world left] (cached world 9 [a])
            [world right] (cached world 9 [b])]
        (compare-exprs world left right 1)))))

(deftest cache-packers-contextualize-before-computing
  (let [world (m/world {}) one (native/native-scalar 1)
        range (native/native-scalar 7)]
    (doseq [[symbol raw normal]
            [["lean_expr_mk_data" [one range one one zero one zero] [1 7 1 1 0 1 0]]
             ["lean_level_mk_data" [one one zero one] [1 1 0 1]]]]
      (is (= (runtime/evaluate ops world symbol normal)
             (runtime/evaluate ops world symbol raw))))
    (let [[world malformed] (m/allocate world :ctor 0 [])]
      (is (thrown-with-msg? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error) #"small Nat"
            (runtime/evaluate ops world "lean_expr_mk_data" [0 malformed 0 0 0 0 0]))))))

#?(:clj
   (deftest mutable-native-metadata-comparison-preserves-borrowed-world
     (let [[world number] (mpz (m/world {}) -1099511627776)
           [world name] (m/allocate world :ctor 2 [zero (native/native-scalar 1)])
           [world child] (cached world 3 [zero])
           [world a] (m/allocate world :ctor 4 [number])
           [world b] (m/allocate world :ctor 4 [-1099511627776])
           [world left] (metadata world name a child)
           [world right] (metadata world name b child)
           world (m/mark-persistent world left)
           machine (u/thaw world) before (u/freeze machine)]
       (is (= 1 (u/runtime-value! machine "lean_expr_equal" [left right])))
       (is (= before (u/freeze machine))))))

#?(:cljs (do (defn -main [] (cljs.test/run-tests 'prototype.runtime-expr-native-test 'prototype.runtime-io-test))
             (set! *main-cli-fn* -main)))
