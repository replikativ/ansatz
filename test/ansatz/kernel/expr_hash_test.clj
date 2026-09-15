(ns ansatz.kernel.expr-hash-test
  "The hash stored in every Expr is Lean's (`Expr.mkData`, expr.h:131): it ignores binder
   names and binder info and mdata payloads, exactly as Lean's `is_equal` — the equality every
   kernel cache uses (LeanExprKey.exprEquals) — does. The invariant the caches rely on is
   `exprEquals(a, b) ⟹ hash(a) == hash(b)`, so `hash(a) != hash(b)` may reject in O(1).
   Expr.equals (intern/shareCommon, Lean's `expr_bi_map`) stays the stricter predicate."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Expr LeanExprKey Level]))

(defn- c [s] (Expr/mkConst (name/from-string s) clojure.lang.PersistentVector/EMPTY false))
(defn- lam [n t b] (Expr/lam (name/from-string n) t b :default))
(defn- pi [n t b] (Expr/forall (name/from-string n) t b :default))
(defn- key= [a b] (.equals (LeanExprKey. a) (LeanExprKey. b)))
(defn- hash= [a b] (= (.structuralHash ^Expr a) (.structuralHash ^Expr b)))

(deftest alpha-variants-hash-equal
  (let [nat (c "Nat") body (Expr/app (c "Nat.succ") (Expr/bvar 0))
        a (lam "x" nat body) b (lam "y" nat body)]
    (testing "a lambda's hash does not depend on the binder name"
      (is (not (identical? a b)))
      (is (hash= a b))
      (is (key= a b) "…and Lean's is_equal identifies them")
      (is (not (.equals a b)) "…while the strict equality intern/shareCommon use does not"))
    (testing "nor on binder info"
      (let [b' (Expr/lam (name/from-string "x") nat body :implicit)]
        (is (hash= a b'))
        (is (key= a b'))))
    (testing "the same for Pi and for nested binders"
      (let [p1 (pi "a" nat (pi "b" nat (Expr/bvar 1)))
            p2 (pi "u" nat (pi "v" nat (Expr/bvar 1)))]
        (is (hash= p1 p2))
        (is (key= p1 p2))
        (is (not (hash= p1 (pi "u" nat (pi "v" nat (Expr/bvar 0))))) "a different body is a different term")))
    (testing "an application of alpha-variant functions"
      (is (hash= (Expr/app a (c "Nat.zero")) (Expr/app b (c "Nat.zero"))))
      (is (key= (Expr/app a (c "Nat.zero")) (Expr/app b (c "Nat.zero")))))))

(deftest mdata-payload-is-not-hashed
  (let [e (c "Nat.zero")
        m1 (Expr/mdata {:a 1} e) m2 (Expr/mdata {:a 2} e)]
    (is (hash= m1 m2) "Lean hashes only the inner expression (Expr.lean:480)")
    (is (not (key= m1 m2)) "is_equal still compares the payload (expr_eq_fn.cpp)")))

(deftest let-binder-name-is-not-hashed
  (let [nat (c "Nat") z (c "Nat.zero")
        l1 (Expr/mkLet (name/from-string "x") nat z (Expr/bvar 0))
        l2 (Expr/mkLet (name/from-string "y") nat z (Expr/bvar 0))]
    (is (hash= l1 l2))
    (is (key= l1 l2))))
