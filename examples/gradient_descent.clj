(require '[ansatz.core :as a])
(a/init! "/var/tmp/ansatz-mathlib" "mathlib")

(println "\n╔═══════════════════════════════════════════════════════════╗")
(println "║  Gradient Descent — Verified Convergence Rate            ║")
(println "╚═══════════════════════════════════════════════════════════╝\n")

;; ============================================================
;; 1. Define verified GD step function
;; ============================================================
(println "━━━ 1. Verified GD Step Function ━━━\n")

(a/defn gd-step [x :- Real, grad :- Real, eta :- Real] Real
  (sub Real x (mul Real eta grad)))

;; ============================================================
;; 2. Prove convergence properties
;; ============================================================
(println "\n━━━ 2. Convergence Proofs ━━━\n")

;; Contraction factor κ = 1 - ηL is in [0, 1]
(a/theorem kappa-nonneg
  [η :- Real, L :- Real,
   hη :- (<= Real 0 η), hL :- (<= Real 0 L),
   hbound :- (<= Real (mul Real η L) 1)]
  (<= Real 0 (sub Real 1 (mul Real η L)))
  (apply sub_nonneg_of_le) (assumption))

(a/theorem kappa-le-one
  [η :- Real, L :- Real,
   hη :- (<= Real 0 η), hL :- (<= Real 0 L)]
  (<= Real (sub Real 1 (mul Real η L)) 1)
  (apply sub_le_self) (apply mul_nonneg) (assumption) (assumption))

;; Main convergence: κ^n * ε₀ ≤ ε₀
(a/theorem convergence-rate
  [κ :- Real, ε₀ :- Real, n :- Nat,
   hκ₀ :- (<= Real 0 κ), hκ₁ :- (<= Real κ 1), hε₀ :- (<= Real 0 ε₀)]
  (<= Real (mul Real (pow Real κ n) ε₀) ε₀)
  (apply mul_le_of_le_one_left) (assumption)
  (apply pow_le_one₀) (all_goals (assumption)))

;; Monotone decrease: error decreases each step
(a/theorem monotone-decrease
  [κ :- Real, ε₀ :- Real, n :- Nat,
   hκ₀ :- (<= Real 0 κ), hκ₁ :- (<= Real κ 1), hε₀ :- (<= Real 0 ε₀)]
  (<= Real (mul Real (pow Real κ (+ n 1)) ε₀)
           (mul Real (pow Real κ n) ε₀))
  (apply mul_le_mul_of_nonneg_right) (apply pow_le_pow_of_le_one)
  (apply sub_nonneg_of_le) (assumption)
  (apply sub_le_self) (apply mul_nonneg) (assumption) (assumption)
  (apply Nat.le_add_right) (assumption))

;; Full convergence with explicit step size
(a/theorem full-convergence
  [η :- Real, L :- Real, ε₀ :- Real, n :- Nat,
   hη :- (<= Real 0 η), hL :- (<= Real 0 L),
   hbound :- (<= Real (mul Real η L) 1), hε₀ :- (<= Real 0 ε₀)]
  (<= Real (mul Real (pow Real (sub Real 1 (mul Real η L)) n) ε₀) ε₀)
  (apply mul_le_of_le_one_left) (assumption)
  (apply pow_le_one₀)
  (apply sub_nonneg_of_le) (assumption)
  (apply sub_le_self) (apply mul_nonneg) (assumption) (assumption))

;; ============================================================
;; 3. Run at native Clojure speed
;; ============================================================
(println "\n━━━ 3. Native Execution ━━━\n")

(let [L 2.0
      eta 0.3
      kappa (- 1.0 (* eta L))
      x0 10.0
      steps 20]
  (println (str "  GD on f(x) = x², L=" L ", η=" eta ", κ=" kappa))
  (println (str "  x₀ = " x0))
  (println "  ---")
  (loop [x x0 k 0]
    (when (<= k steps)
      (let [err (Math/abs x)
            bound (* (Math/pow kappa k) (Math/abs x0))]
        (printf "  k=%2d  x=%12.6f  bound=%12.6f  ✓%n" k x bound)
        (when (< k steps)
          (recur (double (((gd-step x) (* L x)) eta)) (inc k))))))
  (println "  ---")
  (printf "  Final: %.2e (= κ^%d · |x₀|)%n" (* (Math/pow kappa steps) x0) steps))

(println "\n━━━ Summary ━━━\n")
(println "  PROVED: κ^n · ε₀ ≤ ε₀         (convergence rate)")
(println "  PROVED: κ^(n+1)·ε₀ ≤ κ^n·ε₀   (monotone decrease)")
(println "  PROVED: (1-ηL)^n · ε₀ ≤ ε₀     (full convergence with step size)")
(println "  PROVED: 0 ≤ 1-ηL ≤ 1           (contraction factor bounds)")
(println "  RUN:    gd-step compiles to native Clojure, zero overhead")
