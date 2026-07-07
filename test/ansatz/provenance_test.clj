(ns ansatz.provenance-test
  (:require [clojure.test :refer [deftest is testing]]
            [ansatz.provenance :as prov]
            [ansatz.rel :as r]))

(deftest semiring-laws
  (testing "each instance satisfies the semiring identities"
    (doseq [P [prov/boolean-prov prov/maxminprob-prov prov/tropical-prov]]
      (let [z (prov/prov-zero P) o (prov/prov-one P) a (prov/prov-from-prob P 0.5)]
        (is (= a (prov/prov-times P o a)) "one is ⊗-identity")
        (is (= z (prov/prov-times P z a)) "zero is ⊗-annihilator")
        (is (= a (prov/prov-plus P z a)) "zero is ⊕-identity")
        (is (prov/prov-absorptive? P) "the search instances are POPS/recursion-safe")))))

(deftest maxminprob-preserves-log-behavior
  (testing "MaxMinProb tag = the old :logw (⊗=+ on logs, recover=exp)"
    (let [P prov/maxminprob-prov]
      (is (== 0.0 (prov/prov-one P)))
      (is (== (+ (Math/log 0.3) (Math/log 0.5))
              (prov/prov-times P (Math/log 0.3) (Math/log 0.5))))
      (is (< (Math/abs (- 0.15 (prov/prov-recover P (+ (Math/log 0.3) (Math/log 0.5))))) 1e-9)))))

(deftest provenance-pluggable-in-search
  (testing "the SAME search runs under different provenances; heavy clause
            ranks first regardless of the measure algebra"
    (let [g (r/condw [1 r/succeed] [9 r/succeed])]
      (doseq [P [prov/maxminprob-prov prov/tropical-prov prov/boolean-prov]]
        (let [res (r/run 2 (r/state nil :prov P) g)]
          (is (= 2 (count res)) (str "two branches under " (type P)))
          (is (>= (r/order-weight (first res)) (r/order-weight (second res)))
              (str "heavier prior explored first under " (type P)))))
      ;; and the reported MEASURE differs by instance (probability vs cost)
      (let [mm (first (r/run 1 (r/state nil :prov prov/maxminprob-prov) g))
            tr (first (r/run 1 (r/state nil :prov prov/tropical-prov) g))]
        (is (< 0.0 (r/measure mm) 1.0) "MaxMinProb reports a probability")
        (is (< 0.0 (r/measure tr)) "Tropical reports a (positive) cost")))))
