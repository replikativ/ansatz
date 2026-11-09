(ns ansatz.tactic.rw-reducible-test
  "rw matches at reducible transparency; Lean reference: test/lean/rw_reducible.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]))

(use-fixtures :once fixtures/isolated-session
  (fn [f] (binding [a/*verbose* false] (a/load-init!) (f))))

(defn- proves [params goal tactics]
  (a/prove-theorem (gensym "rw_reducible_") params goal tactics)
  true)

(deftest rw-does-not-unfold-instances
  (is (proves '[a :- Nat, b :- Nat,
                h :- (< (Nat.cast Int instNatCastInt a) (Nat.cast Int instNatCastInt b))]
              '(< a b) '[(rw [Int.ofNat_lt] at h) (exact h)])
      "the coercion ↑a is the lemma's spelling")
  (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Did not find an occurrence"
                        (proves '[a :- Nat, b :- Nat, h :- (< (Int.ofNat a) (Int.ofNat b))]
                                '(< a b) '[(rw [Int.ofNat_lt] at h) (exact h)]))
      "Int.ofNat a is ↑a only after unfolding the instance-reducible instNatCastInt"))
