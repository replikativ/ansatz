(ns ansatz.tactic.subst-direction-test
  "Lean pairs: test/lean/subst_direction.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]))

(use-fixtures :once
  (fn [t]
    (a/load-init!)
    (binding [a/*verbose* false *ns* (the-ns 'ansatz.tactic.subst-direction-test)]
      (t))))

(defn- proves [& args]
  (apply a/prove-theorem args)
  true)

(deftest equality-substitution-keeps-left-variable
  (is (true? (proves 'keep-left
                     '[v :- Nat, x :- Nat, h :- (= v x)]
                     '(= v x) '[(subst h) (exact (Eq.refl v))]))))

(deftest subst-vars-searches-variables-in-declaration-order
  (is (true? (proves 'keep-right
                     '[v :- Nat, x :- Nat, h :- (= v x)]
                     '(= v x) '[(subst_vars) (exact (Eq.refl x))]))))

(deftest variable-substitution-eliminates-requested-variable
  (is (true? (proves 'eliminate-left
                     '[v :- Nat, x :- Nat, h :- (= v x)]
                     '(= v x) '[(subst v) (exact (Eq.refl x))])))
  (is (true? (proves 'eliminate-right
                     '[v :- Nat, x :- Nat, h :- (= v x)]
                     '(= v x) '[(subst x) (exact (Eq.refl v))]))))

(deftest substitution-normalizes-sides-and-reintroduces-dependents
  (is (true? (proves 'normalized-right
                     '[v :- Nat, x :- Nat, h :- (= v ((fn [n :- Nat] n) x))]
                     '(= v x) '[(subst h) (exact (Eq.refl v))])))
  (is (true? (proves 'left-fallback
                     '[x :- Nat, h :- (= x 3)]
                     '(= x 3) '[(subst h) (exact (Eq.refl Nat 3))])))
  (is (true? (proves 'dependent-right
                     '[P :- (=> Nat Prop), v :- Nat, x :- Nat,
                       h :- (= v x), hx :- (P x)]
                     '(P v) '[(subst h) (exact hx)]))))

(deftest variable-search-skips-occurring-equation
  (doseq [tactic '[(subst x) (subst_vars)]]
    (is (true? (proves (gensym "skip_occurrence")
                       '[x :- Nat, hbad :- (= x (+ x 1)), hgood :- (= x 3)]
                       '(= x 3) [tactic '(exact (Eq.refl Nat 3))])))))
