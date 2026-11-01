(ns ansatz.omega-conformance-test
  "Paired Init-only omega scripts: test/lean/omega_conformance.lean."
  (:require [clojure.test :refer [deftest]]
            [ansatz.core]
            [ansatz.conformance-support :as cs]))

;; Reference: Lean/Elab/Tactic/Omega/{Frontend,OmegaM,Core}.lean,
;; omegaTactic, asLinearCombo, analyzeAtom, runOmega (checkout in design/omega.md).
;; Surface if uses Bool.rec/Nat.ble; Lean uses ite with a Nat order proposition.
;; Division/modulo/min/max and negative Int use explicit Lean constants; / is Ratio division.
(def ^:private defs
  '[(ansatz.core/defn omegaLen [xs :- (List Nat)] Nat
      (match xs [nil 0] [(cons h t) (+ (omegaLen t) 1)]))])

(def ^:private theorems
  '[[o01_nonneg [x :- Nat]
     (<= Nat 0 x)
     [(omega)]]
    [o02_add_bound [x :- Nat, y :- Nat]
     (<= x (+ x y))
     [(omega)]]
    [o03_succ [x :- Nat, y :- Nat, h :- (<= x y)]
     (< x (Nat.succ y))
     [(omega)]]
    [o04_raw_add [x :- Nat, y :- Nat]
     (= (Nat.add x y) (Nat.add y x))
     [(and_then (simp only [Nat.add_eq]) (omega))]]
    [o05_raw_le [x :- Nat, y :- Nat, z :- Nat, h :- (Nat.le x y), k :- (Nat.le y z)]
     (Nat.le x z)
     [(simp only [Nat.le_eq] at h) (simp only [Nat.le_eq] at k) (simp only [Nat.le_eq]) (omega)]]
    [o06_sub_cancel [x :- Nat, y :- Nat]
     (= (- (+ x y) y) x)
     [(omega)]]
    [o07_sub_trunc [x :- Nat, y :- Nat, h :- (<= x y)]
     (= (- x y) 0)
     [(omega)]]
    [o08_nested_sub [x :- Nat, y :- Nat, z :- Nat, h :- (= (- (- x y) z) 0), k :- (> x (+ y z))]
     False
     [(omega)]]
    [o09_div_lower [x :- Nat]
     (<= (* (Nat.div x 3) 3) x)
     [(omega)]]
    [o10_div_upper [x :- Nat]
     (< x (* (+ (Nat.div x 3) 1) 3))
     [(omega)]]
    [o11_mod_upper [x :- Nat]
     (< Nat (Nat.mod x 3) 3)
     [(omega)]]
    [o12_mod_decomp [x :- Nat]
     (= (+ (Nat.mod x 3) (* 3 (Nat.div x 3))) x)
     [(omega)]]
    [o13_div_zero [x :- Nat]
     (= (Nat.div x 0) 0)
     [(omega)]]
    [o14_int_cancel [x :- Int, y :- Int]
     (= Int (- (+ x y) y) x)
     [(omega)]]
    [o15_int_negative [x :- Int, h :- (<= Int x (Int.negSucc 0))]
     (< Int x 0)
     [(omega)]]
    [o16_parity [x :- Int, y :- Int, h :- (= Int (+ (* 2 x) (* 4 y)) 5)]
     False
     [(omega)]]
    [o17_hard_equality [x :- Nat, y :- Nat, h :- (= (+ (* 6 x) (* 7 y)) 5)]
     False
     [(omega)]]
    [o18_int_div [x :- Int]
     (<= Int (* 2 (HDiv.hDiv Int Int Int (instHDiv Int Int.instDiv) x (Int.ofNat 2))) x)
     [(omega)]]
    [o19_int_mod [x :- Int]
     (And (<= Int 0 (HMod.hMod Int Int Int (instHMod Int Int.instMod) x (Int.ofNat 3)))
          (< Int (HMod.hMod Int Int Int (instHMod Int Int.instMod) x (Int.ofNat 3)) 3))
     [(omega)]]
    [o20_cast [x :- Nat, z :- Int, h :- (< Int 0 z), k :- (<= Int (+ z (Int.ofNat x)) 0)]
     False
     [(omega)]]
    [o21_and_hyp [x :- Int, h :- (And (> Int x 0) (< Int x (Int.negSucc 0)))]
     False
     [(omega)]]
    [o22_or_hyp [x :- Nat, h :- (Or (= x 2) (= x 4))]
     (<= Nat x 4)
     [(omega)]]
    [o23_not_le [x :- Nat, y :- Nat, h :- (Not (<= x y))]
     (< y x)
     [(omega)]]
    [o24_not_and [x :- Nat, h :- (Not (And (<= Nat x 3) (>= Nat x 1))), k :- (>= Nat x 1)]
     (> Nat x 3)
     [(omega)]]
    [o25_iff_hyp [x :- Nat, y :- Nat, h :- (Iff (<= Nat x 3) (<= Nat y 2)), k :- (<= Nat x 3)]
     (<= Nat y 2)
     [(omega)]]
    [o26_iff_goal [x :- Nat]
     (Iff (<= Nat x 0) (= x 0))
     [(omega)]]
    [o27_min [x :- Nat, y :- Nat]
     (<= (Min.min Nat instMinNat x y) x)
     [(omega)]]
    [o28_max [x :- Nat, y :- Nat]
     (<= y (Max.max Nat (maxOfLe Nat instLENat Nat.decLe) x y))
     [(omega)]]
    [o29_if [x :- Nat, y :- Nat]
     (<= x (if (Nat.ble x y) y x))
     [(and_then (split) (omega))]]
    [o30_simp_succ [x :- Nat, y :- Nat, h :- (<= x y)]
     (<= (Nat.succ x) (+ y 1))
     [(and_then (simp only [Nat.succ_eq_add_one]) (omega))]]
    [o31_bool_bridge [x :- Nat, y :- Nat, h :- (= Bool (Nat.ble x y) true)]
     (<= x (+ y 1))
     [(simp only [Nat.ble_eq] at h) (omega)]]
    [o32_induction_simp [xs :- (List Nat)]
     (= (omegaLen xs) (List.length Nat xs))
     [(and_then (induction xs) (and_then (simp only [omegaLen List.length_cons List.length_nil]) (omega)))]]])

(def ^:private known-gaps
  ;; o16_parity and o18_int_div go through since Int scalar products are linearized with
  ;; LinearCombo.mul_eval (Lean Frontend.lean's HMul case).
  {'o19_int_mod "Int remainder needs scalar linearization and emod_def eval-proof transport (omega_proof.clj:954)."})

(deftest omega-conformance
  (let [results (cs/run-suite 'ansatz.omega-conformance-test defs theorems)]
    (doseq [[nm result] results :when (not= :ok result)]
      (println nm "-" (subs result 0 (min 300 (count result)))))
    (cs/check-suite "omega" results known-gaps)))
