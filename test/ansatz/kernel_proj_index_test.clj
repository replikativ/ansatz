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
            [ansatz.kernel.name :as name]
            [ansatz.kernel.reduce :as red])
  (:import [ansatz.kernel Expr Reducer TypeChecker]))

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
      (is (thrown-with-msg? Exception #"invalid projection"
                            (env/check-constant (a/env) d)))))
  (testing "an ordinary projection still checks"
    (let [d (env/mk-def (name/from-string "proj-ok") [] (c "Nat") (Expr/proj (name/from-string "Prod") 1 (pair)))]
      (is (some? (env/check-constant (a/env) d))))))

(defn- pair-of [a b]
  (e/app* (c "Prod.mk" lvl/zero lvl/zero) (c "Nat") (c "Nat") (e/lit-nat a) (e/lit-nat b)))

(defn- proj [i struct] (Expr/proj (name/from-string "Prod") i struct))

(deftest projection-reduction-checks-the-index-before-adding
  (let [r (Reducer. (a/env))]
    (testing "field 1 of Prod.mk Nat Nat 1 2 reduces to 2; field 2 does not exist"
      (is (= (e/lit-nat 2) (.whnf r (proj 1 (pair)))))
      (is (= (proj 2 (pair)) (.whnf r (proj 2 (pair))))))
    (testing "indices that would wrap when the parameter count is added stay unreduced"
      (doseq [i [Integer/MAX_VALUE 4294967296 Long/MAX_VALUE]]
        (is (= (proj i (pair)) (.whnf r (proj i (pair)))) (str "index " i))))
    (testing "the Clojure reducer too"
      (doseq [i [2 Integer/MAX_VALUE Long/MAX_VALUE]]
        (is (= (proj i (pair)) (red/whnf (a/env) (proj i (pair)))) (str "index " i))))))

(deftest lazy-defeq-does-not-truncate-the-index
  ;; field 2^32 truncated to 0 would compare the first components (both 1) and say equal; as in
  ;; Lean, is_def_eq_proof_irrel infers the projection first and infer_proj refuses the index
  (let [tc (TypeChecker. (a/env))]
    (is (thrown-with-msg? Exception #"invalid projection"
                          (.isDefEq tc (proj 4294967296 (pair-of 1 2)) (proj 4294967296 (pair-of 1 3)))))
    (is (true? (.isDefEq tc (proj 0 (pair-of 1 2)) (proj 0 (pair-of 1 3)))))))

(deftest a-missing-field-is-refused-at-admission
  (let [d (env/mk-def (name/from-string "proj-missing") [] (c "Nat") (proj 2 (pair)))]
    (is (thrown? Exception (env/check-constant (a/env) d))))
  (is (thrown? IllegalArgumentException (e/proj (name/from-string "Prod") -0.5 (pair)))))
