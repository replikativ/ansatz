(ns ansatz.tactic.tactic-errors-test
  "Tactic arguments and failure reports; Lean reference: test/lean/tactic_term_args.lean."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]))

(use-fixtures :once fixtures/isolated-session
  (fn [f] (binding [a/*verbose* false] (a/load-init!) (f))))

(defn- proves [params goal tactics]
  (a/prove-theorem (gensym "tactic_errors_") params goal tactics)
  true)

(defn- failure [params goal tactics]
  (try (proves params goal tactics) nil
       (catch clojure.lang.ExceptionInfo ex ex)))

(deftest one-term-arguments
  (testing "(apply f a b) is (apply (f a b)), as Lean parses `apply f a b`"
    (is (proves '[a :- Nat, b :- Nat, h :- (< a b)] '(<= a b) '[(apply Nat.le_of_lt h)]))
    (is (proves '[a :- Nat, b :- Nat, h :- (< a b)] '(<= a b) '[(exact Nat.le_of_lt h)]))
    (is (proves '[a :- Nat, b :- Nat, h :- (< a b)] '(<= a b) '[(refine Nat.le_of_lt h)]))))

(deftest failures-report-the-goal
  (let [ex (failure '[a :- Nat, b :- Nat, h :- (< a b)] '(<= a b) '[(exact h)])
        msg (ex-message ex)]
    (is (re-find #"Type mismatch" msg))
    (is (re-find #"h : LT.lt Nat instLTNat a b" msg) "hypotheses by name")
    (is (re-find #"⊢ LE.le Nat instLENat a b" msg))
    (is (= '(exact h) (:failed-tactic (ex-data ex))))
    (is (string? (:goal-state (ex-data ex)))))
  (testing "a dependent hypothesis shows the variable it mentions, not a free-variable id"
    (let [msg (ex-message (failure '[xs :- (List Nat), h :- (= Nat (List.length Nat xs) 0)]
                                   '(= (List Nat) xs (List.nil Nat)) '[(rfl)]))]
      (is (re-find #"h : .*List.length Nat xs" msg))
      (is (not (re-find #"\?fv" msg))))))
