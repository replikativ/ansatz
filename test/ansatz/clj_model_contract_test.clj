(ns ansatz.clj-model-contract-test
  "The Clojure model contract (ansatz.clj-model.contract): every row's form is translated into
   the model and run against clojure.core on generated EDN. A model answer that differs from
   clojure.core fails the row; so do more no-claims than the row allows. Also keeps
   doc/clojure-model-contract.md equal to the rendering of the table."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.clj-check :as cc]
            [ansatz.clj-model :as m]
            [ansatz.clj-model.contract :as contract]))

(use-fixtures :once fixtures/isolated-session
  (fn [f] (binding [a/*verbose* false] (a/load-init!) (m/install-model!) (f))))

(defn- check-group [group]
  (doseq [row contract/rows :when (= group (:group row))]
    (let [result (cc/run-model-row row)
          {:keys [ok? why]} (cc/model-row-verdict row result)]
      (testing (str (:id row) " " (pr-str (:form row)))
        (is ok? (str (:id row) ": " why))))))

(deftest numbers (check-group :numbers))
(deftest equality (check-group :equality))
(deftest control (check-group :control))
(deftest types (check-group :types))
(deftest collections (check-group :collections))
(deftest sequences (check-group :sequences))
(deftest maps (check-group :maps))
(deftest functions (check-group :functions))
(deftest strings (check-group :strings))
(deftest destructuring (check-group :destructuring))
(deftest recursion (check-group :recursion))

(deftest a-model-without-answers-fails-its-row
  (let [row {:id :probe/none :form '(+ a b) :params '[[a :int] [b :int]] :max-no-claim 0.0}
        result {:counts {:agree 0 :throws 3 :no-claim 40 :model-bug 0}}]
    (is (not (:ok? (cc/model-row-verdict row result))))))

(deftest contract-document-matches-the-table
  (is (= (contract/contract-markdown) (slurp contract/contract-path))
      "doc/clojure-model-contract.md is stale: run (ansatz.clj-model.contract/write-contract!)"))

(deftest every-row-is-well-formed
  (doseq [r contract/rows]
    (is (keyword? (:id r)))
    (is (some #{(:group r)} (map first contract/group-titles)) (str (:id r)))
    (is (number? (:max-no-claim r)) (str (:id r)))
    (is (every? (fn [[p k]] (and (symbol? p) (keyword? k))) (:params r)) (str (:id r))))
  (is (apply distinct? (map :id contract/rows)) "row ids are unique")
  (is (<= 150 (count contract/rows))))
