(ns ansatz.kernel-proj-index-test
  "A projection's field index is Lean's Nat. A negative index used to be typed as field 0 and
   reduced to the constructor's last parameter; it is now refused when the expression is built,
   and the kernel refuses an index outside the int range its field arithmetic uses."
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.core :as a]
            [ansatz.fixtures :as fixtures]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name])
  (:import [ansatz.kernel Expr]))

(defn- setup [f]
  (binding [a/*verbose* false]
    (a/load-init!)
    (f)))

(use-fixtures :once fixtures/isolated-session setup)

(defn- c [s & ls] (e/const' (name/from-string s) (vec ls)))

(defn- pair
  "Prod.mk Nat Nat 1 2"
  []
  (e/app* (c "Prod.mk" lvl/zero lvl/zero) (c "Nat") (c "Nat") (e/lit-nat 1) (e/lit-nat 2)))

(deftest a-negative-projection-index-is-refused
  (testing "building the expression"
    (is (thrown? IllegalArgumentException (Expr/proj (name/from-string "Prod") -1 (pair)))))
  (testing "the kernel refuses an index the int arithmetic would wrap"
    (let [p (Expr/proj (name/from-string "Prod") 4294967296 (pair))
          d (env/mk-def (name/from-string "proj-wrap-bad") [] (c "Nat") p)]
      (is (thrown-with-msg? Exception #"invalid projection index"
                            (env/check-constant (a/env) d)))))
  (testing "an ordinary projection still checks"
    (let [d (env/mk-def (name/from-string "proj-ok") [] (c "Nat") (Expr/proj (name/from-string "Prod") 1 (pair)))]
      (is (some? (env/check-constant (a/env) d))))))
