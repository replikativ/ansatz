(ns ansatz.theory.convergence-test
  "Integration tests for GD convergence proofs.
   Requires Mathlib store at /var/tmp/ansatz-mathlib.
   Skipped if store not available."
  (:require [clojure.test :refer [deftest testing is]]
            [ansatz.core :as a]))

;; ============================================================
;; Mathlib environment
;; ============================================================

(def ^:private mathlib-available?
  (delay
    (try
      (let [store-path "/var/tmp/ansatz-mathlib"]
        (when (.exists (java.io.File. store-path))
          (binding [a/*verbose* false]
            (a/init! store-path "mathlib"))
          ;; Verify env is usable (may fail if store was serialized with old class names)
          (some? (ansatz.kernel.env/lookup (a/env) (ansatz.kernel.name/from-string "Nat")))))
      (catch Exception _ false))))

(defmacro ^:private when-mathlib [& body]
  `(if @mathlib-available?
     (binding [a/*verbose* false] ~@body)
     (is true "skipped: Mathlib store not available")))

;; ============================================================
;; Contraction factor bounds
;; ============================================================

(deftest test-kappa-nonneg
  (when-mathlib
   (testing "0 ≤ 1 - ηL when ηL ≤ 1"
     (a/prove-theorem 'test-kn
                      '[eta :- Real, L :- Real, hb :- (<= Real (mul Real eta L) 1)]
                      '(<= Real 0 (sub Real 1 (mul Real eta L)))
                      '[(apply sub_nonneg_of_le) (assumption)])
     (is true))))

(deftest test-kappa-le-one
  (when-mathlib
   (testing "1 - ηL ≤ 1 when 0 ≤ η, 0 ≤ L"
     (a/prove-theorem 'test-kl
                      '[eta :- Real, L :- Real, heta :- (<= Real 0 eta), hL :- (<= Real 0 L)]
                      '(<= Real (sub Real 1 (mul Real eta L)) 1)
                      '[(apply sub_le_self) (apply mul_nonneg) (assumption) (assumption)])
     (is true))))

;; ============================================================
;; Convergence rate
;; ============================================================

(deftest test-gd-convergence-rate
  (when-mathlib
   (testing "κ^n * ε₀ ≤ ε₀ (error bounded by initial)"
     (a/prove-theorem 'test-gr
                      '[k :- Real, e0 :- Real, n :- Nat,
                        hk0 :- (<= Real 0 k), hk1 :- (<= Real k 1), he0 :- (<= Real 0 e0)]
                      '(<= Real (mul Real (pow Real k n) e0) e0)
                      '[(apply mul_le_of_le_one_left) (assumption)
                        (apply pow_le_one₀) (all_goals (assumption))])
     (is true))))

(deftest test-gd-monotone-decrease
  (when-mathlib
   (testing "κ^(n+1) * ε₀ ≤ κ^n * ε₀ (error decreases each step)"
     (a/prove-theorem 'test-gm
                      '[k :- Real, e0 :- Real, n :- Nat,
                        hk0 :- (<= Real 0 k), hk1 :- (<= Real k 1), he0 :- (<= Real 0 e0)]
                      '(<= Real (mul Real (pow Real k (+ n 1)) e0)
                           (mul Real (pow Real k n) e0))
                      '[(apply mul_le_mul_of_nonneg_right) (apply pow_le_pow_of_le_one)
                        (apply sub_nonneg_of_le) (assumption)
                        (apply sub_le_self) (apply mul_nonneg) (assumption) (assumption)
                        (apply Nat.le_add_right) (assumption)])
     (is true))))

;; ============================================================
;; Full convergence with explicit step size
;; ============================================================

(deftest test-gd-full-convergence
  (when-mathlib
   (testing "Full GD: (1-ηL)^n * ε₀ ≤ ε₀"
     (a/prove-theorem 'test-gf
                      '[eta :- Real, L :- Real, e0 :- Real, n :- Nat,
                        heta :- (<= Real 0 eta), hL :- (<= Real 0 L),
                        hbound :- (<= Real (mul Real eta L) 1), he0 :- (<= Real 0 e0)]
                      '(<= Real (mul Real (pow Real (sub Real 1 (mul Real eta L)) n) e0) e0)
                      '[(apply mul_le_of_le_one_left) (assumption)
                        (apply pow_le_one₀)
                        (apply sub_nonneg_of_le) (assumption)
                        (apply sub_le_self) (apply mul_nonneg) (assumption) (assumption)])
     (is true))))

;; ============================================================
;; Verified function definition + execution
;; ============================================================

(deftest test-gd-step-defn
  (when-mathlib
   (testing "Define and run verified GD step function"
     (let [f (a/define-verified 'test-gd-step
               '[x :- Real, grad :- Real, eta :- Real] 'Real
               '(sub Real x (mul Real eta grad)))]
       (is (fn? f))
        ;; Curried: ((f x) grad) eta)
       (is (= 8.2 (double (((f 10.0) 6.0) 0.3))))))))
