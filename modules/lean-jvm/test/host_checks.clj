(ns host-checks
  "Private adapter checks only; no public import/producer admission evidence."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.lean.jvm.host :as host]
            [ansatz.lean.jvm.typed-value :as typed])
  (:import [ansatz.lean.jvm PureHostCallChecks LeanData]
           [java.util.function Function]))

(defn increment-test [n] (inc n))

(deftest captures-function-value-and-normalizes-clojure-integers
  (let [types (PureHostCallChecks/clojureSignature)
        adapter (host/clojure-implementation types (first types) #'increment-test)]
    ;; inc on java.math.BigInteger yields clojure.lang.BigInt; the adapter
    ;; performs the ordinary typed input conversion before issuing a reply.
    (is (= 42 (PureHostCallChecks/clojureRoundTrip adapter)))
    (with-redefs [increment-test #(+ % 99)]
      (is (= 42 (PureHostCallChecks/clojureRoundTrip adapter)))
      (is (= 140 (PureHostCallChecks/clojureRoundTrip
                   (host/clojure-implementation types (first types) #'increment-test)))))
    (is (thrown? IllegalArgumentException (host/clojure-implementation types (first types) nil)))))

(deftest explicit-arities-and-type-driven-conversion
  (let [nat (first (PureHostCallChecks/clojureSignature))
        ^Function zero (host/clojure-implementation [] nat (fn [] 7N))
        ^Function three (host/clojure-implementation [nat nat nat] nat +)]
    (is (= (biginteger 7) (.apply zero [])))
    (is (= (biginteger 6) (.apply three [1 2 3])))
    (is (thrown? IllegalArgumentException (.apply three [1 2])))))

(deftest custom-datatype-views-and-tagged-map-results
  (let [type (PureHostCallChecks/nominalType)
        adapter (host/clojure-implementation [type] type
                  (fn [{:lean/keys [type constructor fields] :as packet}]
                    (is (some? type))
                    (is (some? constructor))
                    (is (= 42 (first fields)))
                    (update-in packet [:lean/fields 0] inc)))
        ^LeanData result (PureHostCallChecks/nominalRoundTrip adapter)]
    (is (= 43 (first (.fields result))))
    (is (= 43 (first (:lean/fields (typed/view type result)))))))
