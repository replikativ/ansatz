;; Barliman-over-Clojure: everyday surface syntax with holes, filled by
;; measurable relational search, kernel-certified.
(ns ansatz.rel-barliman-test
  (:require [clojure.test :refer [deftest is testing use-fixtures]]
            [ansatz.rel :as r]
            [ansatz.rel.barliman :as b]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.export.parser :as parser]
            [ansatz.export.replay :as replay]))

(def ^:private init-medium-env
  (delay
    (let [f "test-data/init-medium.ndjson"]
      (when (.exists (java.io.File. f))
        (:env (replay/replay (:decls (parser/parse-ndjson-file f))))))))

(def ^:dynamic *env* nil)

(use-fixtures :once
  (fn [f]
    (binding [*env* (or @init-medium-env
                        (throw (ex-info "init-medium.ndjson not found" {})))]
      (f))))

(defn- names [k ms] (mapv #(e/->string (get % k)) ms))

(deftest solve-arithmetic-by-search-and-reduction
  (testing "?x + ?x = 4 : search proposes ?x, the kernel reduces to test"
    (let [{:keys [state expr hole1]} (b/from-surface *env* '(Nat.add ?x ?x) b/NAT)
          sol (r/run 3 state
                     (r/all (b/nat-lito hole1 8)
                            (r/=== expr (b/lit 4))
                            (fn [s] (r/unit (assoc s :x (r/zonk s hole1))))))]
      (is (= ["2"] (names :x sol)))                    ; ?x = 2, and 2+2 reduces to 4
      (is (every? #(:ok? (r/certify % hole1)) sol)))))

(deftest synthesize-operator-disambiguated-by-examples
  (testing "the classic Barliman move: one example is ambiguous, two disambiguate"
    (let [{:keys [state hole1]} (b/from-surface *env* '?op (b/arrows b/NAT b/NAT b/NAT))
          cands (map b/cst ["Nat.add" "Nat.mul" "Nat.sub"])
          exo (fn [a bb out] (r/=== (b/ap hole1 (b/lit a) (b/lit bb)) (b/lit out)))
          run1 (r/run 9 state (r/all (b/oneofo hole1 cands) (exo 2 2 4)
                                     (fn [s] (r/unit (assoc s :op (r/zonk s hole1))))))
          run2 (r/run 9 state (r/all (b/oneofo hole1 cands) (exo 2 2 4) (exo 3 3 6)
                                     (fn [s] (r/unit (assoc s :op (r/zonk s hole1))))))]
      (is (= #{"Nat.add" "Nat.mul"} (set (names :op run1))) "2·2=4: add and mul both fit")
      (is (= ["Nat.add"] (names :op run2)) "3·3=6 kills mul"))))

(deftest everyday-conditional-hole
  (testing "(if ?b 10 20) — fill the condition from the desired result"
    (let [want (fn [w]
                 (let [{:keys [state expr hole1]} (b/from-surface *env* '(if ?b 10 20) b/NAT)]
                   (r/run 2 state
                          (r/all (b/oneofo hole1 (map b/cst ["Bool.true" "Bool.false"]))
                                 (r/=== expr (b/lit w))
                                 (fn [s] (r/unit (assoc s :b (r/zonk s hole1))))))))]
      (is (= ["Bool.true"] (names :b (want 10))))
      (is (= ["Bool.false"] (names :b (want 20)))))))

(deftest value-search-then-proof-then-certify
  (testing "SHOWCASE: elaborate a proposition with a value hole; in ONE search
            fill ?n so ?n+?n=6, then PROVE the equation by refl, and certify"
    (let [prop (e/sort' lvl/zero)
          {:keys [state expr hole1]}
          (b/from-surface *env* '(Eq Nat (Nat.add ?n ?n) 6) prop)
          res (r/run 1 state
                     (r/all
                      (b/nat-lito hole1 12)
                      (r/=== (b/ap (b/cst "Nat.add") hole1 hole1) (b/lit 6))
                      (r/fresh expr
                               (fn [pf]
                                 (r/all (r/applyo pf "Eq.refl" (fn [_] r/succeed))
                                        (fn [s] (r/unit (assoc s :n (r/zonk s hole1)
                                                               :pf pf))))))))
          s (first res)]
      (is (some? s))
      (is (= "3" (e/->string (:n s))))
      (let [c (r/certify s (:pf s))]
        (is (:ok? c) "kernel certifies the refl proof of Nat.add 3 3 = 6")))))
