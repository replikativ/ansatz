(ns ansatz.tactic.positivity-test
  "positivity on the bundled medium Init tier, Int and Nat. Cases are transcribed from
   Mathlib's MathlibTest/positivity.lean (the hypothesis comparisons, numerals, sums,
   products, powers, casts, subtraction under a hypothesis); `0 ≤ x * x` is rejected, as in
   Mathlib (positivity has no `mul_self` extension; nlinarith proves it)."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]))

(defn- with-medium [f]
  (let [saved-env @a/ansatz-env saved-idx @a/ansatz-instance-index]
    (try (binding [a/*verbose* false]
           (binding [*out* (java.io.StringWriter.)] (a/init!))
           (f))
         (finally (reset! a/ansatz-env saved-env)
                  (reset! a/ansatz-instance-index saved-idx)))))

(use-fixtures :once with-medium)

(defmacro ^:private proves [nm params goal]
  `(is (do (a/theorem ~nm ~params ~goal (~'positivity)) true) ~(str nm)))

(defmacro ^:private fails [nm params goal]
  `(is (~'thrown? Exception (a/theorem ~nm ~params ~goal (~'positivity))) ~(str nm)))

(deftest positivity-hypotheses
  (testing "MathlibTest/positivity.lean: comparisons with a numeral in the context"
    (proves pos-h1 [a :- Int, ha :- (< 0 a)] (< 0 a))
    (proves pos-h2 [a :- Int, ha :- (< 0 a)] (<= 0 a))
    (proves pos-h3 [a :- Int, ha :- (< 0 a)] (Ne a 0))
    (proves pos-h4 [a :- Int, ha :- (<= 0 a)] (<= 0 a))
    (proves pos-h5 [a :- Int, ha :- (Ne a 0)] (Ne a 0))
    (proves pos-h6 [a :- Int, ha :- (= Int a 0)] (<= 0 a))
    (proves pos-h7 [a :- Int, ha :- (> a 0)] (>= a 0))
    (proves pos-h8 [a :- Int, ha :- (Ne Int 0 a)] (Ne a 0))
    (proves pos-h9 [a :- Int, ha :- (< 0 a)] (Ne Int 0 a))
    (proves pos-h10 [a :- Int, ha :- (= Int 3 a)] (< 0 a))
    (proves pos-h11 [a :- Int, ha :- (= Int 3 a)] (Ne a 0))
    (proves pos-h12 [a :- Int, ha :- (<= 3 a)] (< 0 a))
    (proves pos-h13 [a :- Int, ha :- (< 3 a)] (Ne a 0))
    (proves pos-h14 [a :- Int, b :- Int, h :- (<= 0 (+ a b))] (<= 0 (+ a b)))
    (proves pos-h15 [a :- Int, hlt :- (<= 0 a), hne :- (Ne a 0)] (< 0 a))))

(deftest positivity-structure
  (testing "numerals, sums, products, powers, casts"
    (proves pos-n1 [] (< Int 0 5))
    (proves pos-n2 [] (Ne Int -3 0))
    (proves pos-s1 [x :- Int, y :- Int, hx :- (< 0 x), hy :- (<= 0 y)] (< 0 (+ x y)))
    (proves pos-s2 [x :- Int] (< 0 (+ (pow x 2) 7)))
    (proves pos-m1 [x :- Int, hx :- (< 3 x)] (< 0 (* x (+ x 1))))
    (proves pos-m2 [x :- Int, hx :- (Ne x 0)] (Ne (* x x) 0))
    (proves pos-p1 [x :- Int] (<= 0 (pow x 2)))
    (proves pos-p2 [x :- Int] (<= 0 (+ (pow x 4) 7)))
    (proves pos-p3 [x :- Int, hx :- (Ne x 0)] (< 0 (pow x 2)))
    (proves pos-p4 [x :- Int, hx :- (< 0 x)] (< 0 (pow x 5)))
    (proves pos-c1 [n :- Nat] (<= Int 0 (Nat.cast Int instNatCastInt n)))
    (proves pos-sub [a :- Int, b :- Int, c :- Int, d :- Int, ha :- (< c a), hb :- (< d b)]
            (< 0 (* (- a c) (- b d))))
    (proves pos-nat1 [n :- Nat] (< 0 (+ n 1)))
    (proves pos-nat2 [n :- Nat, m :- Nat, h :- (< 0 m)] (< 0 (* (+ n 1) m))))
  (testing "what positivity does not prove"
    (fails pos-f1 [x :- Int] (< 0 x))
    (fails pos-f2 [x :- Int] (<= 0 (* x x)))
    (fails pos-f3 [x :- Int, hx :- (<= 0 x)] (< 0 x))))
