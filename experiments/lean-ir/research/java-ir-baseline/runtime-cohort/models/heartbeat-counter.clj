(ns allocation-heartbeat-counter-checks-v1
  (:require [clojure.test :refer [deftest is]] [allocation-heartbeat-counter-v1 :as c]))
(deftest zero-offset-preserves-cumulative-get
  (doseq [raw [0 1 42 Long/MAX_VALUE Long/MIN_VALUE -1]]
    (is (= (mod (bigint raw) c/modulus) (c/read-count raw 0N)))))
(deftest reset-and-subsequent-logical-allocations
  (let [offset (c/set-offset 100 7)]
    (is (= 7N (c/read-count 100 offset)))
    (is (= 9N (c/read-count 102 offset)))
    (is (= 0N (c/read-count 100 (c/set-offset 100 0))))))
(deftest save-work-restore-without-rewinding-cumulative-allocation
  (let [raw-before 1234 saved (c/read-count raw-before 0N)
        raw-after 5000 restored (c/set-offset raw-after (c/result-carrier saved))]
    (is (= 5000 raw-after))
    (is (= saved (c/read-count raw-after restored)))
    (is (= (inc saved) (c/read-count (inc raw-after) restored)))
    ;; Nested restoration is in the same virtual counter domain.
    (let [inner-saved (c/read-count 5005 restored) inner-offset (c/set-offset 9000 (c/result-carrier inner-saved))]
      (is (= inner-saved (c/read-count 9000 inner-offset)))
      (is (= saved (c/read-count 10000 (c/set-offset 10000 (c/result-carrier saved))))))))
(deftest exact-uint64-wrap-and-nat-modulo
  (is (= 0N (c/read-count 0 (c/set-offset -1 (biginteger "18446744073709551615")))) )
  (is (= 0N (c/read-count 123 (c/set-offset 123 (biginteger "18446744073709551616")))) )
  (is (= 42N (c/read-count 123 (c/set-offset 123 (biginteger "18446744073709551658")))) )
  (is (= 18446744073709551615N (c/read-count -1 0N)))
  (is (= 9223372036854775808N (c/read-count Long/MIN_VALUE 0N)))
  (is (= 1N (c/read-count Long/MIN_VALUE (c/set-offset Long/MAX_VALUE 0)))))
(deftest result-carriers-preserve-full-uint64
  (is (instance? Long (c/result-carrier 42N)))
  (is (instance? Long (c/result-carrier (bigint Long/MAX_VALUE))))
  (is (instance? java.math.BigInteger (c/result-carrier (inc (bigint Long/MAX_VALUE)))))
  (is (= (biginteger "18446744073709551615") (c/result-carrier (dec c/modulus)))))
(deftest branch-values-diverge-without-shared-mutation
  (let [parent-offset (c/set-offset 200 99) child-offset parent-offset
        child-next (c/set-offset 250 0)]
    (is (= 109N (c/read-count 210 parent-offset)))
    (is (= 109N (c/read-count 210 child-offset)))
    (is (= 0N (c/read-count 250 child-next)))
    (is (= 149N (c/read-count 250 parent-offset)))))
(deftest malformed-and-explicit-bit-bound
  (doseq [bad [-1 -1N (biginteger -1) 0N (Integer/valueOf 1) 1.0 nil (Object.)]]
    (is (thrown? clojure.lang.ExceptionInfo (c/set-offset 0 bad))))
  (is (integer? (c/set-offset 0 (.shiftLeft java.math.BigInteger/ONE 4095))))
  (is (thrown? clojure.lang.ExceptionInfo (c/set-offset 0 (.shiftLeft java.math.BigInteger/ONE 4096))))
  (is (thrown? clojure.lang.ExceptionInfo (c/read-count 0 -1N)))
  (is (thrown? clojure.lang.ExceptionInfo (c/read-count 0 c/modulus)))
  (is (thrown? clojure.lang.ExceptionInfo (c/read-count 0N 0N))))

(deftest fork-rebases-different-raw-allocation-mark
  (let [parent-raw 500 parent-offset (c/set-offset parent-raw 123)
        child-raw 10 child-offset (c/fork-offset parent-raw parent-offset child-raw)]
    (is (= 123N (c/read-count child-raw child-offset)))
    (is (= 124N (c/read-count (inc child-raw) child-offset)))
    (is (not= 123N (c/read-count child-raw parent-offset))))
  (is (= 7N (c/read-count Long/MIN_VALUE (c/fork-offset 100 (c/set-offset 100 7) Long/MIN_VALUE)))))

(deftest bigint-subclass-rejected-before-overridable-methods
  (let [calls (atom 0)
        value (proxy [java.math.BigInteger] ["0"]
                (signum [] (swap! calls inc) 0)
                (bitLength [] (swap! calls inc) 0)
                (longValue [] (swap! calls inc) 0))]
    (reset! calls 0)
    (is (thrown? clojure.lang.ExceptionInfo (c/set-offset 0 value)))
    (is (zero? @calls))))
