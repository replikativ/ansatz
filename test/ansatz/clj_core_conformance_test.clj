(ns ansatz.clj-core-conformance-test
  "The clojure.core contract table (ansatz.clj-contract) against the bundled Init: every row's
   form is defined with a/defn and run against the same form evaluated by clojure.core.
   A row's :expect is today's status; :diverges rows are strict expected failures (a fix must
   flip the row). Rows whose constants the bundled Init lacks are skipped here and run in
   ansatz.clj-core-conformance-mathlib-test."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.clj-check :as cc]
            [ansatz.clj-contract :as contract]))

(defn- init-once [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (cc/run-setup! contract/setup-forms)
    (f)))

(use-fixtures :once fixtures/isolated-session init-once)

(defn- check-group [group]
  (doseq [row contract/rows :when (= group (:group row))]
    (let [result (cc/run-row row)
          {:keys [ok? why]} (cc/row-verdict row result)]
      (testing (str (:id row) " " (pr-str (:form row)))
        (is ok? (str (:id row) ": " why))))))

(deftest arithmetic (check-group :arithmetic))
(deftest comparison (check-group :comparison))
(deftest control (check-group :control))
(deftest bodies (check-group :bodies))
(deftest data (check-group :data))

(deftest the-harness-finds-the-known-divergence
  (testing "Nat subtraction: a witness with b > a"
    (let [row (first (filter #(= :sub/nat (:id %)) contract/rows))
          {:keys [witnesses]} (cc/run-row row)
          {:keys [args clojure ansatz]} (first witnesses)]
      (is (< (first args) (second args)))
      (is (neg? clojure))
      (is (zero? ansatz)))))

(deftest representation-round-trips
  (testing "Option is tagged when Ansatz runs alone"
    (is (= [5] (cc/clj->runtime [:option [:nat]] 5)))
    (is (nil? (cc/clj->runtime [:option [:nat]] nil)))
    (is (= 5 (cc/runtime->clj [:option [:nat]] [5]))))
  (testing "results agree across Long/BigInt, NaN, and nil vs the empty list"
    (is (cc/agree? [:nat] 3 3N))
    (is (cc/agree? [:float] Double/NaN Double/NaN))
    (is (not (cc/agree? [:float] 0.5 0.25)))
    (is (cc/agree? [:list [:nat]] nil ()))
    (is (not (cc/agree? [:list [:nat]] [1] [1 2])))))
