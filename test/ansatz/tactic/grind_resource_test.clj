(ns ansatz.tactic.grind-resource-test
  "Init-only recursive coverage regression; paired with grind_coverage.lean."
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.tactic.grind.action :as action]))

(use-fixtures :once
  (fn [f]
    (let [before @a/ansatz-env]
      (try
        (a/load-init!)
        (binding [a/*verbose* false
                  *ns* (the-ns 'ansatz.tactic.grind-resource-test)]
          (f))
        (finally (reset! a/ansatz-env before))))))

(deftest recursive-coverage-stays-within-preprocessing-budget
  ;; Reconstructing a record from projections can multiply the traversal cost
  ;; even when E-matching generates only a few hundred graph nodes.
  (a/structure CovHandle [] (id Nat) (spin Nat) (reachable Bool) (touched Bool) (dropped Bool))
  (a/structure CovEntity [] (id Nat) (tokens (List Nat)))
  (a/defn covmem [x :- Nat, xs :- (List Nat)] Bool
    (match xs [nil false]
      [(cons h t) (if (Nat.beq x h) true (covmem x t))]))
  (a/defn covone [h :- CovHandle, e :- CovEntity] Bool
    (if (Nat.beq (:spin h) (:id e))
        (Bool.and
          (if (:dropped h) (Bool.not (covmem (:id h) (:tokens e))) true)
          (if (Bool.and (:reachable h) (Bool.and (:touched h) (Bool.not (:dropped h))))
              (covmem (:id h) (:tokens e)) true))
        true))
  (a/defn covall [h :- CovHandle, es :- (List CovEntity)] Bool
    (match es [nil true]
      [(cons e t) (Bool.and (covone h e) (covall h t))]))
  (a/deftheorem cov-one-loss [h :- CovHandle, e :- CovEntity]
    (=> (= (covone h e) true)
        (= (covone (CovHandle.mk (:id h) (:spin h) false (:touched h) (:dropped h)) e) true))
    (grind [covone]))
  (let [result (try
                 (a/prove-theorem
                  'cov-loss
                  '[h :- CovHandle, es :- (List CovEntity)]
                  '(=> (= (covall h es) true)
                       (= (covall (CovHandle.mk (:id h) (:spin h) false (:touched h) (:dropped h)) es) true))
                  '[(induction es) (simp [covall]) (intro hc) (grind [covall cov-one-loss])])
                 :proved
                 (catch clojure.lang.ExceptionInfo ex
                   (if (= :tactic-error (:kind (ex-data ex))) (ex-data ex) (throw ex))))]
    (is (or (= :proved result) (= :max-steps (:limit result))) (str result))))

(deftest preprocessing-step-limit-is-configurable
  (let [term (reduce (fn [t _] (e/app t t)) (e/fvar 0) (range 12))]
    (binding [action/*config* (action/configure {:max-steps 100})]
      (let [error (try (action/check-expr! term)
                       (catch clojure.lang.ExceptionInfo ex ex))]
        (is (= :tactic-error (:kind (ex-data error))))
        (is (= :max-steps (:limit (ex-data error))))
        (is (= 100 (:used (ex-data error))))))
    (is (nil? (action/check-expr! term)))))
