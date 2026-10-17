(ns prototype.runtime-expr-transform-portable-test
  (:require [prototype.machine :as m] [prototype.runtime-expr :as expr]
            [prototype.runtime-expr-transform :as transform] [prototype.scalar :as scalar]
            #?(:clj [clojure.test :refer [deftest is]]
               :cljs [cljs.test :refer-macros [deftest is]])))
(def ops {:ref? m/ref? :node m/node :allocate m/allocate :retain m/retain :release m/release :replace-node m/replace-node})
(defn setup []
  (let [[world root] (m/scalar-constructor (m/world {}) 0 [0] {:objects 1 :usize 0 :ssize 8})
        ;; The no-op cases need only a valid exact range/flags cache; this uses
        ;; the production packer while avoiding unsupported full64 JS hashing.
        cache (second (expr/evaluate ops world "lean_expr_mk_data" [123 1 0 0 0 0 0]))
        layout (:layout (m/node world root))
        memory (scalar/write-bytes layout {} {:index 1 :offset 0 :type "uint64" :region :scalar} cache)
        world (assoc-in world [:heap (:id root) :scalar-bytes] memory)
        [world empty] (m/allocate world :array 246 [])]
    [world root empty]))
(deftest unchanged-transform-results-are-owned-and-leave-snapshots-intact
  (let [[world root empty] (setup)]
    (doseq [[symbol args] [["lean_expr_abstract_range" [root 0 empty]]
                           ["lean_expr_instantiate" [root empty]]
                           ["lean_expr_instantiate_range" [root 0 0 empty]]
                           ["lean_expr_lift_loose_bvars" [root 0 0]]]]
      (let [[next result] (transform/evaluate ops world symbol args)]
        (is (= root result))
        (is (= 2 (:rc (m/node next root))))
        (is (= (:heap world) (:heap (m/release next result 1))))))))
(deftest invalid-ranges-fail-before-any-guest-allocation-or-ownership-change
  (let [[world root empty] (setup)]
    (doseq [symbol ["lean_expr_instantiate_range" "lean_expr_instantiate_rev_range"]]
      (is (thrown? #?(:clj clojure.lang.ExceptionInfo :cljs js/Error)
             (transform/evaluate ops world symbol [root 1 0 empty]))))
    (is (= 1 (:rc (m/node world root))))))
#?(:cljs
   (deftest full64-reconstruction-is-explicitly-outside-the-js-number-profile
     (let [[world root _] (setup)]
       (is (thrown? js/Error (transform/evaluate ops world "lean_expr_lift_loose_bvars" [root 0 1]))))))
