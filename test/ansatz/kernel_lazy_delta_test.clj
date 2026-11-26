(ns ansatz.kernel-lazy-delta-test
  "Lazy delta reduction keeps the pair it is comparing in its own locals. It used to keep it in
   one array on the checker, which a nested isDefEq overwrote: reducing `Nat.succ q` to a
   literal ran whnf of q, whose Eq.rec reduction by K compared `a = b` with `a = a` and left
   `a, a` in the array; the outer comparison then found no definition to unfold, returned
   'unknown', and its caller read the nested pair and called the two sides equal."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]))

(defn- setup [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (f)))

(use-fixtures :once fixtures/isolated-session setup)

(defn- n [s] (name/from-string s))
(defn- c [s & ls] (e/const' (n s) (vec ls)))
(def ^:private one (lvl/succ lvl/zero))
(def ^:private nat (c "Nat"))
(defn- eq-nat [x y] (e/app* (c "Eq" one) nat x y))

(defn- environment
  "a : Nat (an axiom), b := a, h : a = b, q := @Eq.rec Nat a (fun _ _ => Nat) a b h — so q
   reduces to a, by K on h."
  []
  (let [ax (fn [env nm ty] (env/check-constant env (env/mk-axiom (n nm) [] ty)))
        df (fn [env nm ty v] (env/check-constant env (env/mk-def (n nm) [] ty v)))
        motive (e/lam-default (n "x") nat
                              (e/lam-default (n "hx") (eq-nat (c "lazy-delta-a") (e/bvar 0)) nat))
        q (e/app* (c "Eq.rec" one one) nat (c "lazy-delta-a") motive (c "lazy-delta-a")
                  (c "lazy-delta-b") (c "lazy-delta-h"))]
    (-> (a/env)
        (ax "lazy-delta-a" nat)
        (df "lazy-delta-b" nat (c "lazy-delta-a"))
        (ax "lazy-delta-h" (eq-nat (c "lazy-delta-a") (c "lazy-delta-b")))
        (df "lazy-delta-q" nat q))))

(deftest a-nested-comparison-does-not-replace-the-outer-pair
  (let [env (environment)
        a' (c "lazy-delta-a")
        thm (fn [nm goal proof] (env/mk-thm (n nm) [] goal proof))
        refl-a (e/app* (c "Eq.refl" one) nat a')]
    (testing "q does reduce to a: q = a holds by rfl"
      (is (some? (env/check-constant env (thm "lazy-delta-ok" (eq-nat (c "lazy-delta-q") a') refl-a)))))
    (testing "Nat.succ q = a is refused (it would give Nat.succ a = a)"
      (is (thrown-with-msg? Exception #"does not match declared type"
                            (env/check-constant env (thm "lazy-delta-bad"
                                                         (eq-nat (e/app (c "Nat.succ") (c "lazy-delta-q")) a')
                                                         refl-a))))
      (is (thrown-with-msg? Exception #"does not match declared type"
                            (env/check-constant env (thm "lazy-delta-bad'"
                                                         (eq-nat a' (e/app (c "Nat.succ") (c "lazy-delta-q")))
                                                         refl-a)))))))
