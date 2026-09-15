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

(deftest structural-equality-on-shared-dags
  ;; expr_eq_fn memoizes the composite pairs it enters: two structurally equal DAGs built
  ;; separately (no pointer sharing between them, heavy sharing within each) compare once per
  ;; shared pair instead of once per path.
  (let [nat (c "Nat")
        tower (fn [depth]
                (loop [e (Expr/app (c "f") (Expr/bvar 0)) d 0]
                  (if (= d depth) e (recur (Expr/app (Expr/app (c "g") e) e) (inc d)))))
        a (lam "x" nat (tower 40)) b (lam "y" nat (tower 40))]
    (is (not (identical? a b)))
    (is (hash= a b))
    (is (key= a b) "2^40 paths, compared in linear time")
    (is (not (key= a (lam "y" nat (Expr/app (c "g") (tower 39))))))))

(deftest pair-memo-is-an-identity-set
  (let [m (ansatz.kernel.LeanExprKey$PairMemo.)
        xs (vec (repeatedly 300 #(Expr/app (c "h") (c "Nat.zero"))))]
    (is (.add m (xs 0) (xs 1)))
    (is (not (.add m (xs 0) (xs 1))) "a present pair is reported")
    (is (.add m (xs 1) (xs 0)) "…ordered")
    (is (.add m (xs 0) (xs 2)))
    (doseq [i (range 3 300)] (.add m (xs i) (xs (dec i))))
    (is (= 300 (.size m)) "growth keeps every pair")
    (is (not (.add m (xs 150) (xs 149))))))

(deftest expr-map-is-lean-s-expr-map
  ;; expr_map: keys under is_equal — an alpha-variant key hits, a different term does not,
  ;; and the identity fast path is the same entry.
  (let [m (ansatz.kernel.ExprMap. 4)
        nat (c "Nat") body (Expr/app (c "Nat.succ") (Expr/bvar 0))
        a (lam "x" nat body) b (lam "y" nat body)]
    (.put m a :a)
    (is (= :a (.get m a)))
    (is (= :a (.get m b)) "alpha-variant key")
    (is (nil? (.get m (lam "x" nat (Expr/bvar 0)))))
    (.put m b :b)
    (is (= 1 (.size m)) "the alpha-variant is the same key")
    (is (= :b (.get m a)))
    (doseq [i (range 500)] (.put m (Expr/litNat i) i))
    (is (= 501 (.size m)) "growth keeps every entry")
    (is (= 250 (.get m (Expr/litNat 250))))
    (is (= :b (.get m a)))
    (.clear m)
    (is (zero? (.size m)))
    (is (nil? (.get m a)))))

(deftest expr-pair-set-is-lean-s-expr-pair-set
  (let [ps (ansatz.kernel.ExprPairSet. 4)
        nat (c "Nat") body (Expr/app (c "Nat.succ") (Expr/bvar 0))
        a (lam "x" nat body) a' (lam "y" nat body) z (c "Nat.zero")]
    (is (not (.contains ps a z)))
    (.add ps a z)
    (is (.contains ps a z))
    (is (.contains ps a' z) "pairs are compared under is_equal")
    (is (not (.contains ps z a)) "…and ordered")
    (.add ps a' z)
    (is (= 1 (.size ps)))
    (doseq [i (range 500)] (.add ps (Expr/litNat i) (Expr/litNat (inc i))))
    (is (= 501 (.size ps)))
    (is (.contains ps (Expr/litNat 300) (Expr/litNat 301)))
    (is (not (.contains ps (Expr/litNat 301) (Expr/litNat 300))))
    (is (.contains ps a z))))
