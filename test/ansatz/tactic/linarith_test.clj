(ns ansatz.tactic.linarith-test
  "linarith and nlinarith on the bundled medium Init tier (no Mathlib), Int and Nat.

   Cases are transcribed from Mathlib's MathlibTest/Tactic/Linarith/Basic.lean (the Int and
   Nat ones; Rat examples whose certificates need no division are restated over Int), plus
   the bounded-arithmetic obligations a client discharges when it proves two programs over
   checked 64-bit Int arithmetic equal: nonlinear bounds from interval hypotheses, and the
   64-bit range of a polynomial once its nonlinear atoms are bounded. Every proof is checked
   by the kernel when the theorem is admitted."
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

(defmacro ^:private proves [nm params goal & tactics]
  `(is (do (a/theorem ~nm ~params ~goal ~@tactics) true) ~(str nm)))

(defmacro ^:private fails [nm params goal & tactics]
  `(is (~'thrown? Exception (a/theorem ~nm ~params ~goal ~@tactics)) ~(str nm)))

(deftest linarith-int
  (testing "MathlibTest/Tactic/Linarith/Basic.lean, Int"
    (proves lin-int-1 [h :- (< Int 1 0), g :- (Not (< Int 37 42)), l :- (< Int -7 5)] (< Int 3 7) (linarith))
    (proves lin-int-2 [x :- Int, y :- Int, z :- Int, h1 :- (< (* 2 x) (* 3 y)),
                       h2 :- (< (+ (* -4 x) (* 2 z)) 0), h3 :- (< (- (* 12 y) (* 4 z)) 0)]
            False (linarith))
    (proves lin-int-3 [x :- Int, y :- Int, z :- Int, h1 :- (< (* 2 x) (* 3 y)),
                       h2 :- (< (+ (* -4 x) (* 2 z)) 0), h3 :- (< (* x y) 5),
                       h4 :- (< (- (* 12 y) (* 4 z)) 0)]
            False (linarith))
    (proves lin-int-4 [x :- Int, y :- Int, z :- Int, h1 :- (< (* 2 x) (* 3 y)),
                       h2 :- (< (+ (* -4 x) (* 2 z)) 0), h3 :- (< (* x y) 5)]
            (Not (< (- (* 12 y) (* 4 z)) 0)) (linarith))
    (proves lin-int-5 [w :- Int, x :- Int, y :- Int, z :- Int,
                       h1 :- (<= (+ (+ (* 4 x) (* -3 y)) (* 6 w)) 0), h2 :- (< (* -1 x) 0),
                       h3 :- (< y 0), h4 :- (>= w 0)]
            False (linarith))
    (proves lin-int-6 [i :- Int, hi :- (> i 5)] (> (+ (* 2 i) 3) 11) (linarith))
    (proves lin-int-7 [k :- Int, h :- (< k 1), h1 :- (< -1 k)] (= Int k 0) (linarith))
    (proves lin-int-8 [a :- Int, b :- Int, c :- Int, h1 :- (> a 0), h2 :- (> b 5), h3 :- (< c -10),
                       h4 :- (< (- (+ a b) c) 3)]
            False (linarith))
    (proves lin-int-9 [x :- Int, y :- Int, z :- Int, hx :- (<= x (* 3 y)), h2 :- (<= y (* 2 z)),
                       h3 :- (>= x (* 6 z))]
            (= Int x (* 3 y)) (linarith))
    (proves lin-int-10 [x :- Int, y :- Int, h :- (< x y)] (Not (= Int x y)) (linarith))
    (proves lin-int-11 [a :- Int, ha :- (<= 0 a)] (<= (* 0 0) (* 2 a)) (linarith)))
  (testing "a conjunction hypothesis is split"
    (proves lin-int-and [x :- Int, y :- Int, h :- (And (<= 0 y) (<= 1 x))] (<= 1 (+ y x)) (linarith)))
  (testing "term arguments and `only`"
    (proves lin-int-only [x :- Int, y :- Int, h1 :- (< x y), h2 :- (< y 0)] (< x 0) (linarith only [h1 h2]))
    (fails lin-int-only-short [x :- Int, y :- Int, h1 :- (< x y), h2 :- (< y 0)] (< x 0) (linarith only [h1]))
    (proves lin-int-term [x :- Int, h :- (< 0 x)] (<= 0 (+ x x)) (linarith only [(Int.le_of_lt h)])))
  (testing "a goal that does not follow is refused"
    (fails lin-int-false [x :- Int, h :- (<= x 4)] (<= x 3) (linarith))
    (fails lin-int-nonlinear [x :- Int, h :- (<= 0 x)] (<= 0 (* x x)) (linarith))))

(deftest linarith-nat
  (testing "MathlibTest/Tactic/Linarith/Basic.lean, Nat (moved to Int)"
    (proves lin-nat-1 [h1 :- (< Nat 1 1)] False (linarith))
    (proves lin-nat-2 [a :- Nat, b :- Nat] (>= (+ a b) a) (linarith))
    (proves lin-nat-3 [a :- Nat, b :- Nat, i :- Nat, h1 :- (Not (< a i)), h2 :- (< b i), h3 :- (<= a b)]
            False (linarith))
    (proves lin-nat-4 [x :- Nat, y :- Nat, z :- Nat, hx :- (<= x (* 3 y)), h2 :- (<= y (* 2 z)),
                       h3 :- (>= x (* 6 z))]
            (= Nat x (* 3 y)) (linarith))
    (proves lin-nat-5 [a :- Nat, b :- Nat] (Not (< (+ a b) a)) (linarith))
    (proves lin-nat-6 [n :- Nat, h1 :- (<= n 3), h2 :- (> n 2)] (= Nat n 3) (linarith))
    (proves lin-nat-7 [z :- Nat, hz :- (Not (>= z 2)), h2 :- (Not (<= (+ z 1) 2))] False (linarith))
    (proves lin-nat-8 [z :- Nat, hz :- (Not (>= z 2))] (<= (+ z 1) 2) (linarith))
    (proves lin-nat-9 [p :- Nat, n :- Nat, p' :- Nat, n' :- Nat, h :- (= Nat (+ p n') (+ p' n))]
            (= Nat (+ n p') (+ n' p)) (linarith))))

(deftest nlinarith-int
  (testing "MathlibTest/Tactic/Linarith/Basic.lean nlinarith examples, over Int"
    (proves nlin-1 [x :- Int, y :- Int] (<= 0 (+ (pow x 2) (pow y 2))) (nlinarith))
    (proves nlin-2 [x :- Int, y :- Int] (<= 0 (+ (* x x) (* y y))) (nlinarith))
    (proves nlin-3 [x :- Int, y :- Int, hx :- (= Int x 0), hy :- (= Int y 0)] (= Int (+ (* x x) (* y y)) 0) (nlinarith))
    (proves nlin-4 [x :- Int, y :- Int, h1 :- (= Int (+ (* x x) (* y y)) 0)] (= Int x 0) (nlinarith))
    (proves nlin-5 [x :- Int, y :- Int, h1 :- (<= (+ (* x x) (* y y)) 0)] (= Int y 0) (nlinarith))
    (proves nlin-6 [x :- Int] (<= 0 (* x x)) (nlinarith))
    (proves nlin-7 [a :- Int, b :- Int, ha :- (< 0 a), hb :- (< 0 b)] (< 0 (* a b)) (nlinarith))))

(deftest client-bounded-int-obligations
  (testing "nonlinear bounds from interval hypotheses"
    (proves cb-square [i :- Int, h1 :- (<= -1048576 i), h2 :- (<= i 1048576)]
            (<= (* i i) 1099511627776) (nlinarith))
    (proves cb-square-lower [i :- Int] (<= 0 (* i i)) (nlinarith))
    (proves cb-product-upper [a :- Int, b :- Int, ha1 :- (<= -1000 a), ha2 :- (<= a 1000),
                              hb1 :- (<= -1000 b), hb2 :- (<= b 1000)]
            (<= (* a b) 1000000) (nlinarith))
    (proves cb-product-lower [a :- Int, b :- Int, ha1 :- (<= -1000 a), ha2 :- (<= a 1000),
                              hb1 :- (<= -1000 b), hb2 :- (<= b 1000)]
            (<= -1000000 (* a b)) (nlinarith))
    (proves cb-triple-upper [a :- Int, b :- Int, c :- Int, hab1 :- (<= -1000000 (* a b)),
                             hab2 :- (<= (* a b) 1000000), hc1 :- (<= -1000 c), hc2 :- (<= c 1000)]
            (<= (* (* a b) c) 1000000000) (nlinarith))
    (proves cb-poly-upper [i :- Int, h1 :- (<= -1048576 i), h2 :- (<= i 1048576)]
            (<= (+ (- (* 3 (* i i)) (* 2 i)) 7) 3298536980487) (nlinarith))
    (proves cb-poly-lower [i :- Int, h1 :- (<= -1048576 i), h2 :- (<= i 1048576)]
            (<= -2097145 (+ (- (* 3 (* i i)) (* 2 i)) 7)) (nlinarith)))
  (testing "64-bit range once the nonlinear atoms are bounded (linear, large constants)"
    (proves cb-range-upper [i :- Int, h1 :- (<= -1048576 i), h2 :- (<= i 1048576),
                            h3 :- (<= (* i i) 1099511627776), h4 :- (<= 0 (* i i))]
            (<= (+ (- (* 3 (* i i)) (* 2 i)) 7) 9223372036854775807) (linarith))
    (proves cb-range-lower [i :- Int, h1 :- (<= -1048576 i), h2 :- (<= i 1048576),
                            h3 :- (<= (* i i) 1099511627776), h4 :- (<= 0 (* i i))]
            (<= -9223372036854775808 (+ (- (* 3 (* i i)) (* 2 i)) 7)) (linarith))))
