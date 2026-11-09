(ns ansatz.elab-expected-type-test
  "Positions that determine a term's type; Lean reference: test/lean/expected_type_positions.lean."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]))

(use-fixtures :once fixtures/isolated-session
  (fn [f] (binding [*ns* (the-ns 'ansatz.elab-expected-type-test) a/*verbose* false]
            (a/load-init!) (f))))

(defn- run-fn [sym] @(ns-resolve 'ansatz.elab-expected-type-test sym))

(defn- proves [params goal tactics]
  (a/prove-theorem (gensym "expected_type_") params goal tactics)
  true)

(deftest nested-match-has-its-own-result-type
  (testing "a match under a constructor is not at the enclosing match's result type"
    (a/defn et-pick [o :- (Option Bool), u :- Nat, e :- Nat] (Option Nat)
      (match o [(some v) (Option.some Nat (match v [true u] [false e]))] [none (Option.none Nat)]))
    (is (= [[5] [7] nil] (mapv #((run-fn 'et-pick) % 5 7) [[true] [false] nil]))))
  (testing "a match in tail position is"
    (a/defn et-keep [o :- (Option Bool), u :- Nat] (Option Nat)
      (match o [(some v) (match v [true (Option.some Nat u)] [false (Option.none Nat)])]
             [none (Option.none Nat)]))
    (is (= [[4] nil nil] (mapv #((run-fn 'et-keep) % 4) [[true] [false] nil])))))

(deftest apply-numeral-takes-the-goal-type
  (is (proves '[] '(Exists (fn [n :- Nat] (= Nat n n))) '[(apply (Exists.intro 0)) (rfl)]))
  (is (proves '[] '(Exists (fn [n :- Int] (= Int n n))) '[(apply (Exists.intro 0)) (rfl)])
      "the Nat default waits until apply has matched the goal")
  (is (proves '[] '(Exists (fn [n :- Int] (= Int n 3))) '[(apply (Exists.intro 3)) (rfl)])))
