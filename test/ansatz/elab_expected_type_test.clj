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
      (match o (some v) (Option.some Nat (match v true u false e)) none (Option.none Nat)))
    (is (= [5 7 nil] (mapv #((run-fn 'et-pick) % 5 7) [true false nil]))))
  (testing "a match in tail position is"
    (a/defn et-keep [o :- (Option Bool), u :- Nat] (Option Nat)
      (match o (some v) (match v true (Option.some Nat u) false (Option.none Nat))
             none (Option.none Nat)))
    (is (= [4 nil nil] (mapv #((run-fn 'et-keep) % 4) [true false nil])))))

(deftest explicit-result-for-an-intermediate-match
  (a/defn et-head [b :- Bool] Nat
    (match (match-as b Bool (List Nat)
                     (true nil)
                     (false [4]))
      nil 7
      (cons x _) x))
  (is (= [7 4] (mapv (run-fn 'et-head) [true false]))))

(deftest apply-numeral-takes-the-goal-type
  (is (proves '[] '(Exists (fn [n :- Nat] (= Nat n n))) '[(apply (Exists.intro 0)) (rfl)]))
  (is (proves '[] '(Exists (fn [n :- Int] (= Int n n))) '[(apply (Exists.intro 0)) (rfl)])
      "the Nat default waits until apply has matched the goal")
  (is (proves '[] '(Exists (fn [n :- Int] (= Int n 3))) '[(apply (Exists.intro 3)) (rfl)])))

(deftest negative-numerals-are-never-nat-literals
  ;; A kernel Nat literal is a natural number (Expr.litNat refuses a negative value): a negative
  ;; surface integer is `-n` at the position's type, Int when nothing fixes one.
  (testing "at a typed position"
    (a/defn et-dec3 [x :- Int] Int (+ x -3))
    (is (= 2 ((run-fn 'et-dec3) 5)))
    (a/defn et-neg-body [x :- Int] Int -7)
    (is (= -7 ((run-fn 'et-neg-body) 0)))
    (is (proves '[x :- Int] '(= Int (+ x -1) (- x 1)) '[(omega)])))
  (testing "a comparison of two numerals runs at Int"
    (a/defn et-neg-cmp [x :- Int] Bool (< -2 -1))
    (is (true? ((run-fn 'et-neg-cmp) 0))))
  (testing "at Nat it is an error, not a literal"
    (is (thrown? Exception (a/defn et-neg-nat [x :- Nat] Nat -1)))))
