(ns ansatz.surface.if-comparison-carrier-test
  "An `if` over a comparison takes the comparison's carrier from its operands, as
   the Bool comparison does. Before, the lift to `dite` hard-coded Nat
   (`LT.lt Nat instLTNat`, `Nat.decLt`), so `(if (< i 0) ..)` with `i : Int` was a
   type error, as was any if over an Int or Bool comparison; a literal branch
   next to an Int branch stayed a Nat; and well-founded recursion read every
   if-guard as a Nat proposition."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.env :as kenv]
            [ansatz.kernel.name :as kn]))

(defn- init-once [f]
  (binding [a/*verbose* false] (a/load-init!) (f)))

(use-fixtures :once init-once)

(defn- value-str [n] (str (.getValue (kenv/lookup (a/env) (kn/from-string (str n))))))

(deftest int-conditions-lift-at-int
  (testing "an Int variable against a literal, in both orders"
    (a/defn icc-lt [i :- Int] Int (if (< i 0) (- 0 i) i))
    (a/defn icc-lt' [i :- Int] Int (if (< 0 i) i 0))
    (a/defn icc-gt [i :- Int] Int (if (> i 3) 3 i))
    (a/defn icc-gt' [i :- Int] Int (if (> 3 i) i 3))
    (a/defn icc-le [i :- Int] Int (if (<= i 3) 1 2))
    (a/defn icc-le' [i :- Int] Int (if (<= 3 i) 1 2))
    (a/defn icc-ge [i :- Int] Int (if (>= i 3) 1 2))
    (a/defn icc-ge' [i :- Int] Int (if (>= 3 i) 1 2))
    (a/defn icc-eq [i :- Int] Int (if (== i 7) 1 2))
    (a/defn icc-eq' [i :- Int] Int (if (== 7 i) 1 2))
    (is (= [4 5] [(icc-lt -4) (icc-lt 5)]))
    (is (= [0 5] [(icc-lt' -1) (icc-lt' 5)]))
    (is (= [3 2] [(icc-gt 9) (icc-gt 2)]))
    (is (= [-2 3] [(icc-gt' -2) (icc-gt' 9)]))
    (is (= [1 2] [(icc-le 3) (icc-le 4)]))
    (is (= [1 2] [(icc-le' 3) (icc-le' 2)]))
    (is (= [1 2] [(icc-ge 3) (icc-ge 2)]))
    (is (= [1 2] [(icc-ge' 3) (icc-ge' 4)]))
    (is (= [1 2] [(icc-eq 7) (icc-eq -7)]))
    (is (= [1 2] [(icc-eq' 7) (icc-eq' 8)])))
  (testing "two Int variables"
    (a/defn icc-max [i :- Int, j :- Int] Int (if (< i j) j i))
    (is (= [9 2 -1] [(icc-max 2 9) (icc-max 2 -5) (icc-max -1 -1)])))
  (testing "the guard is the canonical Int proposition, so dite's branches carry it"
    (is (re-find #"dite" (value-str 'icc-lt)))
    (is (re-find #"Int\.decLt" (value-str 'icc-lt)))
    (is (re-find #"Int\.decLe" (value-str 'icc-le)))
    (is (re-find #"Int\.decEq" (value-str 'icc-eq)))))

(deftest literal-branches-take-the-if-s-type
  (a/defn icc-clamp0 [i :- Int] Int (if (< 0 i) i 0))
  (is (= [5 0] [(icc-clamp0 5) (icc-clamp0 -5)]))
  (testing "nested ifs in the definition body take its declared type"
    (a/defn icc-sign [i :- Int] Int (if (< i 0) -1 (if (== i 0) 0 1)))
    (is (= [-1 0 1] [(icc-sign -3) (icc-sign 0) (icc-sign 8)]))))

(deftest other-carriers-take-the-bool-path
  (a/defn icc-pick [b :- Bool] Nat (if (== b true) 1 2))
  (is (= [1 2] [(icc-pick true) (icc-pick false)]))
  (is (not (re-find #"dite" (value-str 'icc-pick)))))

(deftest nat-conditions-are-unchanged
  (a/defn icc-nclamp [n :- Nat] Nat (if (< n 3) n 3))
  (is (= [2 3] [(icc-nclamp 2) (icc-nclamp 7)]))
  (is (re-find #"Nat\.decLt" (value-str 'icc-nclamp)))
  (testing "well-founded recursion over Nat still sees its guard"
    (a/defn icc-halves [n :- Nat] Nat :termination-by n
      (if (<= n 1) 0 (+ 1 (icc-halves (- n 2)))))
    (is (= 3 (icc-halves 6)))))
