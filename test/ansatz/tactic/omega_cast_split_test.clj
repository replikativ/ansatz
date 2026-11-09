(ns ansatz.tactic.omega-cast-split-test
  "omega splits ↑(Int.toNat x) and ↑(Int.natAbs x); Lean reference:
   test/lean/omega_cast_split.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]))

(use-fixtures :once fixtures/isolated-session
  (fn [f] (binding [a/*verbose* false] (a/load-init!) (f))))

(defn- omega? [params goal]
  (a/prove-theorem (gensym "omega_cast_split_") params goal '[(omega)])
  true)

(defn- cast [x] (list 'Nat.cast 'Int 'instNatCastInt x))

(deftest to-nat-and-nat-abs-are-split
  (is (omega? '[x :- Int, h :- (<= 0 x)] (list '= 'Int (cast '(Int.natAbs x)) 'x)))
  (is (omega? '[x :- Int, h :- (<= 0 x)] (list '= 'Int (cast '(Int.toNat x)) 'x)))
  (is (omega? '[x :- Int] (list '<= 0 (cast '(Int.toNat x)))))
  (is (omega? '[x :- Int, h :- (< x 0)] '(= Nat (Int.toNat x) 0)))
  (is (omega? '[x :- Int, h :- (< x 0)] (list '= 'Int (cast '(Int.natAbs x)) '(- x))))
  (is (omega? '[x :- Int] (list '<= 'x (cast '(Int.natAbs x)))))
  (is (omega? '[x :- Int, y :- Int]
              (list '<= (cast '(Int.natAbs (+ x y))) (list '+ (cast '(Int.natAbs x)) (cast '(Int.natAbs y)))))
      "triangle inequality: one split per natAbs atom")
  (is (thrown? Exception (omega? '[x :- Int, h :- (<= 0 x)] (list '= 'Int (cast '(Int.natAbs x)) '(+ x 1))))))
