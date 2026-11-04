(ns ansatz.rewrite-beta-test
  (:require [clojure.test :refer [deftest is use-fixtures]]
            [ansatz.core :as a]
            [ansatz.test-env :as test-env]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]))

(use-fixtures :once
  (fn [t]
    (let [saved @a/ansatz-env]
      (try
        (reset! a/ansatz-env @test-env/checked-bundled-init-env)
        (binding [*ns* (the-ns 'ansatz.rewrite-beta-test)]
          (a/defn beta-all [p :- (=> Nat Bool), xs :- (List Nat)] Bool
            (match xs [nil true] [(cons h t) (Bool.and (p h) (beta-all p t))]))
          (a/defn beta-g [n :- Nat] Nat n)
          (a/theorem beta-g-eq [n :- Nat] (= (beta-g n) n) (rfl))
          (a/theorem beta-one [p :- (=> Nat Bool), n :- Nat]
                     (= (beta-all p (List.cons Nat n (List.nil Nat))) (Bool.and (p n) true)) (rfl))
          (t))
        (finally (reset! a/ansatz-env saved))))))

(defn- verified? [nm]
  (let [ci (env/lookup (a/env) (name/from-string nm))]
    (and ci (env/verifies? (a/env) (.type ci) (.value ci)))))

(deftest rewrite-instantiated-function-in-hypothesis
  (a/theorem beta-hyp [x :- Nat,
                       h :- (= (beta-all (fn [r :- Nat] (Nat.beq (beta-g r) 0))
                                         (List.cons Nat x (List.nil Nat))) true)]
             (= (Bool.and (Nat.beq x 0) true) true)
             (rw [beta-one] at h)
             (rw [beta-g-eq] at h)
             (exact h))
  (is (verified? "beta-hyp")))

(deftest rewrite-instantiated-function-in-goal
  (a/theorem beta-goal [x :- Nat, h :- (= (Bool.and (Nat.beq x 0) true) true)]
             (= (beta-all (fn [r :- Nat] (Nat.beq (beta-g r) 0))
                          (List.cons Nat x (List.nil Nat))) true)
             (rw [beta-one])
             (rw [beta-g-eq])
             (exact h))
  (is (verified? "beta-goal")))

(deftest rewrite-instantiated-function-with-nested-applications
  (a/defn beta-apply-two [f :- (=> Nat Nat Bool), x :- Nat, y :- Nat] Bool (f x y))
  (a/theorem beta-apply-two-eq [f :- (=> Nat Nat Bool), x :- Nat, y :- Nat]
             (= (beta-apply-two f x y) (f x y)) (rfl))
  (a/theorem beta-nested [x :- Nat, y :- Nat, h :- (= (Nat.beq x y) true)]
             (= (beta-apply-two (fn [r :- Nat, s :- Nat] (Nat.beq (beta-g r) (beta-g s))) x y) true)
             (rw [beta-apply-two-eq])
             (rw [beta-g-eq])
             (exact h))
  (is (verified? "beta-nested")))

(deftest reverse-rewrite-instantiates-function-before-beta-reduction
  (a/theorem beta-one-reverse [p :- (=> Nat Bool), n :- Nat]
             (= (Bool.and (p n) true) (beta-all p (List.cons Nat n (List.nil Nat)))) (rfl))
  (a/theorem beta-reverse [x :- Nat,
                           h :- (= (beta-all (fn [r :- Nat] (Nat.beq (beta-g r) 0))
                                             (List.cons Nat x (List.nil Nat))) true)]
             (= (Bool.and (Nat.beq x 0) true) true)
             (rw [<- beta-one-reverse] at h)
             (rw [beta-g-eq] at h)
             (exact h))
  (is (verified? "beta-reverse")))
