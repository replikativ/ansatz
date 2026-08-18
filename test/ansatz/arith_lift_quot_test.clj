(ns ansatz.arith-lift-quot-test
  "`quot` and `rem` lift to Nat.div / Nat.mod, and `/` deliberately does not.

  Clojure's `/` on integers is RATIO division -- `(/ 7 3)` is `7/3` -- while
  `Nat.div` is floor division. Lifting `/` would make a verified definition
  mean something other than the Clojure it erases to, which is the one thing
  that must not happen. `quot` IS truncating integer division, and on Nat that
  is floor division, so the surface spelling and the emitted code agree."
  (:require [clojure.test :refer [deftest testing is use-fixtures]]
            [ansatz.core :as a]))

(defn- init-once [f]
  (binding [a/*verbose* false] (a/load-init!) (f)))

(use-fixtures :once init-once)

(deftest quot-lifts-and-emits-quot
  (testing "a verified definition using quot compiles, and the emitted Clojure
            uses quot rather than /"
    (binding [a/*verbose* false]
      (a/defn third [n Nat] Nat (quot n 3))
      (is (= 0 (third 0)))
      (is (= 0 (third 2)))
      (is (= 1 (third 3)))
      (is (= 33 (third 100)))
      (testing "and agrees with Clojure's quot on the same inputs"
        (is (every? true? (for [n (range 200)] (= (quot n 3) (third n)))))))))

(deftest rem-lifts
  (binding [a/*verbose* false]
    (a/defn r3 [n Nat] Nat (rem n 3))
    (is (every? true? (for [n (range 200)] (= (rem n 3) (r3 n)))))))

(deftest quot-is-provable
  (testing "the point of lifting it: a theorem over a quot-using definition"
    (binding [a/*verbose* false]
      (a/defn q2 [n Nat] Nat (quot n 2))
      (a/theorem quot-two-of-zero []
                 (= Nat (q2 0) 0)
                 (grind))
      (is true "theorem proved"))))

(deftest slash-is-not-lifted
  (testing "`/` must NOT elaborate to floor division -- it means Ratio
            division in Clojure, and a verified definition that silently
            changed meaning on erasure would defeat the purpose"
    (binding [a/*verbose* false]
      (is (thrown? clojure.lang.ExceptionInfo
                   (a/defn bad [n Nat] Nat (/ n 3)))))))
