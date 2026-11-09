(ns ansatz.tactic.simp-arg-placeholder-test
  "simp argument placeholders; Lean reference: test/lean/simp_arg_placeholder.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]))

(use-fixtures :once fixtures/isolated-session
  (fn [f] (binding [a/*verbose* false] (a/load-init!) (f))))

(defn- proves [params goal tactics]
  (a/prove-theorem (gensym "simp_arg_placeholder_") params goal tactics)
  true)

(deftest placeholders-become-lemma-parameters
  (is (proves '[n :- Nat] '(= Nat (+ n 0) n) '[(simp only [(Nat.add_zero _)])]))
  (is (proves '[n :- Nat, m :- Nat] '(= Nat (+ (+ n 0) (+ m 0)) (+ n m))
              '[(simp only [(Nat.add_zero _)])])
      "one abstracted lemma rewrites both instances")
  (is (proves '[n :- Nat, h :- (= Nat (+ n 0) 5)] '(= Nat n 5)
              '[(simp only [(Nat.add_zero _)] at h) (exact h)]))
  (is (proves '[n :- Nat, m :- Nat] '(= Nat (+ n m) (+ m n)) '[(simp only [(Nat.add_comm n _)])]))
  (is (proves '[n :- Nat] '(= Nat (+ n 0) n) '[(simp only [(Nat.add_zero n)])])
      "a closed term is unchanged"))
