(ns ansatz.tactic.omega-int-scalar-test
  "omega on Int goals with scalar products, negative literals and literals beyond 64 bits,
   through the surface `(omega)` on the bundled medium Init tier. Linear cases are from
   Lean's tests/lean/run/omega.lean (its Int examples with `k * x`); the large-literal cases
   are the checked 64-bit arithmetic bounds a client needs.

   What these pin: `k * x` over Int is linear (LinearCombo.mul_eval with Int.mul_congr, as
   Lean's Frontend.lean HMul case), a Nat product with a large literal is one multiplication
   rather than k additions, negative literals elaborate to `-n`, bounds past 2^63 stay exact,
   and two comparisons over different large literals are never compared by unfolding."
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
  `(is (do (a/theorem ~nm ~params ~goal (~'omega)) true) ~(str nm)))

(deftest int-scalar-products
  (testing "tests/lean/run/omega.lean, Int with literal coefficients"
    (proves om-s1 [x :- Int, y :- Int, h1 :- (> (+ x y) 10), h2 :- (< (* 2 x) 11), h3 :- (< y 5)] False)
    (proves om-s2 [x :- Int, y :- Int, h :- (= Int (+ (* 2 x) (* 4 y)) 5)] False)
    (proves om-s3 [x :- Int, h :- (= Int (+ (* 2 x) 1) 0)] False)
    (proves om-s4 [x :- Int, h1 :- (<= 1 (* -3 x)), h2 :- (<= 1 (* 2 x))] False)
    (proves om-s5 [x :- Int, y :- Int, h1 :- (= Int (+ (* 2 x) (* 3 y)) 0), h2 :- (<= 1 x), h3 :- (<= 1 y)] False)
    (proves om-s6 [x :- Int, y :- Int, h1 :- (<= 1 (* 3 x)), h2 :- (<= y 2), h3 :- (<= (- (* 6 x) 2) y)] False)
    (proves om-s7 [x :- Int, y :- Int, z :- Int, h1 :- (< (* 2 x) (* 3 y)), h2 :- (< (+ (* -4 x) (* 2 z)) 0),
                   h3 :- (< (- (* 12 y) (* 4 z)) 0)] False)
    (proves om-s8 [x :- Int, y :- Int, z :- Int, hx :- (<= x (* 3 y)), h2 :- (<= y (* 2 z)), h3 :- (>= x (* 6 z))]
            (= Int x (* 3 y)))
    (proves om-s9 [x :- Int, h :- (<= (* x 7) 100)] (<= x 14))))

(deftest large-literals
  (testing "bounds at and beyond the 64-bit range"
    (proves om-l1 [x :- Int, h :- (<= 9223372036854775808 x)] (<= 9223372036854775807 x))
    (proves om-l2 [x :- Int, h :- (<= -9223372036854775808 x)] (<= -9223372036854775809 x))
    (proves om-l3 [x :- Int, y :- Int, h1 :- (<= -1048576 x), h2 :- (<= x 1048576), h3 :- (<= 0 y),
                   h4 :- (<= y 1099511627776)]
            (<= (+ (* 3 y) (* -2 x)) 9223372036854775807))
    (proves om-l4 [x :- Nat, h :- (<= x 1099511627776)] (<= (* 1099511627776 x) 1208925819614629174706176))
    (proves om-l5 [x :- Int, h1 :- (<= -9223372036854775808 x), h2 :- (<= x 9223372036854775807)]
            (<= (- x 1) 9223372036854775806))))
