(ns prototype.fingerprint-test
  (:require [clojure.test :refer [deftest is]]
            [prototype.fingerprint :as fingerprint]
            [prototype.machine :as m]))

(deftype PoisonLiteral []
  Object
  (hashCode [_] (throw (Exception. "Literal hashCode must not run")))
  (equals [_ _] (throw (Exception. "Literal equals must not run")))
  (toString [_] (throw (Exception. "Literal toString must not run"))))

(defn deep-body [depth leaf]
  (loop [n depth body [:return [:imm leaf]]]
    (if (zero? n) body
      (recur (dec n) [:inc [:var 1] 1 false body]))))

(deftest deep-ir-is-stack-safe-and-matches-independent-construction
  (let [left (deep-body 4000 42) right (deep-body 4000 42) changed (deep-body 4000 43)
        a (fingerprint/key left) b (fingerprint/key right)]
    (is (= a b))
    (is (not= a (fingerprint/key changed)))
    (is (= 64 (count (first a))))
    (is (re-matches #"[0-9a-f]{64}" (first a)))))

(deftest map-set-and-parse-order-do-not-affect-content
  (is (= (fingerprint/key (array-map :left [:var 1] :right {:b 2 :a 1}))
         (fingerprint/key (array-map :right (array-map :a 1 :b 2) :left [:var 1]))))
  (is (= (fingerprint/key #{:a :b [:var 1]}) (fingerprint/key (sorted-set-by #(compare (str %1) (str %2)) :b [:var 1] :a))))
  (is (= (fingerprint/key (read-string "[:let 3 [:literal {:b 2 :a 1}] [:return [:var 3]]]"))
         (fingerprint/key (read-string "[:let 3 [:literal {:a 1 :b 2}] [:return [:var 3]]]"))))
  (is (not= (fingerprint/key {:a 1 :b 2}) (fingerprint/key {:a 2 :b 1}))))

(deftest collections-records-and-literals-remain-distinct
  (is (not= (fingerprint/key [:var 1]) (fingerprint/key '(:var 1))))
  (is (not= (fingerprint/key (m/->Tag 0)) (fingerprint/key {:tag 0})))
  (is (= (fingerprint/key (m/->Tag 0)) (fingerprint/key (m/->Tag 0))))
  (is (not= (fingerprint/key (m/->Tag 1)) (fingerprint/key (m/->Ref 1))))
  (is (not= (fingerprint/key (m/->Builtin :inc)) (fingerprint/key {:name :inc})))
  (is (not= (fingerprint/key :literal) (fingerprint/key 'literal)))
  (is (not= (fingerprint/key (long 1)) (fingerprint/key (int 1))))
  (is (not= (fingerprint/key 0.0) (fingerprint/key -0.0)))
  (is (not= (fingerprint/key (String. (char-array [(char 55296)])))
            (fingerprint/key (String. (char-array [(char 55297)])))))
  (is (not= (fingerprint/key ["a" "b"]) (fingerprint/key ["a\u0000b"]))))

(deftest opaque-identity-never-calls-literal-equality-hash-or-print
  (let [a (PoisonLiteral.) b (PoisonLiteral.)]
    (is (= (fingerprint/key [:literal a]) (fingerprint/key [:literal a])))
    (is (not= (fingerprint/key [:literal a]) (fingerprint/key [:literal b])))
    (is (= (fingerprint/key (array-map :a a :b b))
           (fingerprint/key (array-map :b b :a a)))))
  (let [cyclic (java.util.ArrayList.)]
    (.add cyclic cyclic)
    (is (= (fingerprint/key cyclic) (fingerprint/key cyclic)))))

(deftest memo-is-identity-indexed-and-bounded
  (fingerprint/clear-cache!)
  (try
    (let [body (deep-body 4000 42) first-key (fingerprint/key body)]
      (dotimes [_ 10] (is (identical? first-key (fingerprint/key body))))
      (is (= {:entries 1 :hits 10 :misses 1}
             (select-keys (fingerprint/cache-stats) [:entries :hits :misses]))))
    (fingerprint/clear-cache!)
    (let [first-value [:literal :first] first-key (fingerprint/key first-value)
          limit (:limit (fingerprint/cache-stats))]
      (dotimes [i limit] (fingerprint/key [:literal i]))
      (is (= limit (:entries (fingerprint/cache-stats))))
      (is (= first-key (fingerprint/key first-value)))
      (is (= (+ limit 2) (:misses (fingerprint/cache-stats))))
      (is (= limit (:entries (fingerprint/cache-stats)))))
    (finally (fingerprint/clear-cache!))))

(deftest concurrent-calculation-keeps-content-and-cache-correct
  (fingerprint/clear-cache!)
  (try
    (let [body (deep-body 200 :done) workers (doall (repeatedly 8 #(future (fingerprint/key body))))
          keys (mapv deref workers)]
      (is (every? #(= (first keys) %) keys))
      (is (= 1 (:entries (fingerprint/cache-stats)))))
    (finally (fingerprint/clear-cache!))))
