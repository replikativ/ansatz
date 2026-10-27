import Init

-- Adapted from lean4/tests/lean/run/omega.lean and omega_examples.lean.
-- Raw heads and final simp/Bool probes model the simp → omega boundary.
def omegaLen : List Nat → Nat
  | [] => 0
  | _ :: xs => omegaLen xs + 1

theorem o01_nonneg (x : Nat) : 0 ≤ x := by
  omega

theorem o02_add_bound (x y : Nat) : x ≤ x + y := by
  omega

theorem o03_succ (x y : Nat) (h : x ≤ y) : x < Nat.succ y := by
  omega

theorem o04_raw_add (x y : Nat) : Nat.add x y = Nat.add y x := by
  simp only [Nat.add_eq] <;> omega

theorem o05_raw_le (x y z : Nat) (h : Nat.le x y) (k : Nat.le y z) : Nat.le x z := by
  simp only [Nat.le_eq] at h k ⊢; omega

theorem o06_sub_cancel (x y : Nat) : x + y - y = x := by
  omega

theorem o07_sub_trunc (x y : Nat) (h : x ≤ y) : x - y = 0 := by
  omega

theorem o08_nested_sub (x y z : Nat) (h : x - y - z = 0) (k : x > y + z) : False := by
  omega

theorem o09_div_lower (x : Nat) : x / 3 * 3 ≤ x := by
  omega

theorem o10_div_upper (x : Nat) : x < (x / 3 + 1) * 3 := by
  omega

theorem o11_mod_upper (x : Nat) : x % 3 < 3 := by
  omega

theorem o12_mod_decomp (x : Nat) : x % 3 + 3 * (x / 3) = x := by
  omega

theorem o13_div_zero (x : Nat) : x / 0 = 0 := by
  omega

theorem o14_int_cancel (x y : Int) : x + y - y = x := by
  omega

theorem o15_int_negative (x : Int) (h : x ≤ -1) : x < 0 := by
  omega

theorem o16_parity (x y : Int) (h : 2*x + 4*y = 5) : False := by
  omega

theorem o17_hard_equality (x y : Nat) (h : 6*x + 7*y = 5) : False := by
  omega

theorem o18_int_div (x : Int) : 2 * (x / 2) ≤ x := by
  omega

theorem o19_int_mod (x : Int) : 0 ≤ x % 3 ∧ x % 3 < 3 := by
  omega

theorem o20_cast (x : Nat) (z : Int) (h : 0 < z) (k : z + (x : Int) ≤ 0) : False := by
  omega

theorem o21_and_hyp (x : Int) (h : x > 0 ∧ x < -1) : False := by
  omega

theorem o22_or_hyp (x : Nat) (h : x = 2 ∨ x = 4) : x ≤ 4 := by
  omega

theorem o23_not_le (x y : Nat) (h : ¬ x ≤ y) : y < x := by
  omega

theorem o24_not_and (x : Nat) (h : ¬ (x ≤ 3 ∧ x ≥ 1)) (k : x ≥ 1) : x > 3 := by
  omega

theorem o25_iff_hyp (x y : Nat) (h : x ≤ 3 ↔ y ≤ 2) (k : x ≤ 3) : y ≤ 2 := by
  omega

theorem o26_iff_goal (x : Nat) : x ≤ 0 ↔ x = 0 := by
  omega

theorem o27_min (x y : Nat) : min x y ≤ x := by
  omega

theorem o28_max (x y : Nat) : y ≤ max x y := by
  omega

theorem o29_if (x y : Nat) : x ≤ (if x ≤ y then y else x) := by
  split <;> omega

theorem o30_simp_succ (x y : Nat) (h : x ≤ y) : Nat.succ x ≤ y + 1 := by
  simp only [Nat.succ_eq_add_one] <;> omega

theorem o31_bool_bridge (x y : Nat) (h : Nat.ble x y = true) : x ≤ y + 1 := by
  simp only [Nat.ble_eq] at h; omega

theorem o32_induction_simp (xs : List Nat) : omegaLen xs = xs.length := by
  induction xs <;> simp only [omegaLen, List.length_cons, List.length_nil] <;> omega
