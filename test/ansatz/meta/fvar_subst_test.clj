(ns ansatz.meta.fvar-subst-test
  (:require [clojure.test :refer [deftest is]]
            [ansatz.kernel.expr :as e]
            [ansatz.meta.fvar-subst :as s]))

(deftest insert-composes-ranges-without-replacing-existing-domain-entries
  (let [x (e/fvar 1) y (e/fvar 2)
        subst (-> {} (s/insert 1 y) (s/insert 2 (e/lit-nat 9)))]
    (is (= (e/lit-nat 9) (s/get subst 1)))
    (is (= (e/lit-nat 9) (s/get subst 2)))
    (is (= subst (s/insert subst 1 x)))
    (is (= x (s/get (s/erase subst 1) 1)))
    (is (nil? (s/find? subst 3)))
    (is (= #{1 2} (set (s/domain subst))))
    (is (s/any (fn [k _] (= k 2)) subst))))

(deftest append-is-sequential-composition
  (let [expr (e/app (e/fvar 1) (e/fvar 3))
        first {1 (e/fvar 2)} second {2 (e/lit-nat 4) 3 (e/lit-nat 8)}]
    (is (= (s/apply second (s/apply first expr)) (s/apply (s/append first second) expr)))))
