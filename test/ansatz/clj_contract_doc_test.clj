(ns ansatz.clj-contract-doc-test
  "doc/clojure-contract.md is generated from the contract table; it must not drift from it."
  (:require [clojure.test :refer [deftest is]]
            [ansatz.clj-contract :as contract]))

(deftest contract-document-matches-the-table
  (is (= (contract/contract-markdown) (slurp contract/contract-path))
      "doc/clojure-contract.md is stale: run (ansatz.clj-contract/write-contract!)"))

(deftest every-row-is-well-formed
  (doseq [r contract/rows]
    (is (keyword? (:id r)))
    (is (contains? #{:agree :refuse :diverges :domain} (:expect r)) (str (:id r)))
    (is (vector? (:params r)) (str (:id r))))
  (is (apply distinct? (map :id contract/rows)) "row ids are unique"))
