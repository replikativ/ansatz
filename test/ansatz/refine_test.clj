(ns ansatz.refine-test
  "A2 — refinement-fact extraction from kernel types (the read-side inverse of the malli functor).
   Pure/fast: builds types via ansatz.malli/schema->type-expr and decodes them back; no Init env."
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.refine :as r]
            [ansatz.malli :as malli]))

(deftest nat-range-decode
  (testing "bounded :int schemas round-trip through the Subtype encoding back to {:min :max}"
    (is (= {:min 3 :max 9} (r/nat-range (malli/schema->type-expr [:int {:min 3 :max 9}]))))
    (is (= {:min 5}        (r/nat-range (malli/schema->type-expr [:int {:min 5}]))))
    (is (= {:max 99}       (r/nat-range (malli/schema->type-expr [:int {:max 99}]))))
    (is (= {:min 1 :max 7} (r/nat-range (malli/schema->type-expr [:and :int [:>= 1] [:< 8]]))))
    (testing "values are plain longs, not BigInteger (clean selectivity arithmetic)"
      (is (every? #(instance? Long %) (vals (r/nat-range (malli/schema->type-expr [:int {:min 3 :max 9}]))))))))

(deftest no-false-refinement
  (testing "an unbounded scalar carries no range fact"
    (is (nil? (r/nat-range (malli/schema->type-expr :int))))
    (is (nil? (r/nat-range (malli/schema->type-expr :boolean))))
    (testing "a Subtype over a non-Nat base does not masquerade as a Nat range"
      ;; string length bound is a Subtype String — not a value-domain Nat range
      (is (nil? (r/nat-range (malli/schema->type-expr [:string {:min 2}])))))))

(deftest structural-facts
  (testing "the functor's structural shapes are recovered as facts"
    (is (= :list   (:kind (r/type-facts (malli/schema->type-expr [:vector :int])))))
    (is (= :option (:kind (r/type-facts (malli/schema->type-expr [:maybe :int])))))
    (is (= :subtype (:kind (r/type-facts (malli/schema->type-expr [:int {:min 0 :max 5}])))))
    (testing "the List elem type is itself queryable (lattice descends into collections)"
      (let [lf (r/type-facts (malli/schema->type-expr [:vector [:int {:min 2 :max 4}]]))]
        (is (= :list (:kind lf)))
        (is (= {:min 2 :max 4} (r/nat-range (:elem lf))))))))

(deftest refinement-pred-available
  (testing "the raw refinement predicate is recoverable for filter-elimination obligations"
    (is (some? (r/refinement-pred (malli/schema->type-expr [:int {:min 3}]))))
    (is (nil?  (r/refinement-pred (malli/schema->type-expr :int))))))
