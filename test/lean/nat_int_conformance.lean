-- Lean 4.33.1 reference; paired with test/ansatz/nat_int_conformance_test.clj.
-- Scripts follow Lean.Elab.Tactic.Induction.evalInductionCore/evalCasesCore,
-- Simp.evalSimp and Decide.evalDecideCore in src/Lean/Elab/Tactic/.
set_option linter.unusedSimpArgs false
def tally : List Nat → Nat
  | [] => 0
  | _ :: t => tally t + 1
def total : List Nat → Nat
  | [] => 0
  | h :: t => h + total t
def zeros : Nat → Nat
  | 0 => 0
  | n+1 => zeros n + 0
def power (a : Nat) : Nat → Nat
  | 0 => 1
  | n+1 => power a n * a
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n
def peak : List Nat → Nat
  | [] => 0
  | h :: t => if h ≤ peak t then peak t else h
def itotal : List Int → Int
  | [] => 0
  | h :: t => h + itotal t

theorem n01_zeros (n : Nat) : zeros n = 0 := by
  induction n <;> simp [zeros, *]

theorem n02_tally_nonneg (xs : List Nat) : 0 ≤ tally xs := by
  omega

theorem n03_tally_cons (x : Nat) (xs : List Nat) : tally (x :: xs) > tally xs := by
  simp [tally]

theorem n04_total_cons (x : Nat) (xs : List Nat) : total xs ≤ total (x :: xs) := by
  simp [total] <;> omega

theorem n05_total_zero (xs : List Nat) (h : total xs = 0) (x : Nat) : total (x :: xs) = x := by
  simp [total, h]

theorem n06_sub_self (xs : List Nat) : total xs - total xs = 0 := by
  omega

theorem n07_sub_truncate (xs : List Nat) (n : Nat) (h : total xs ≤ n) : total xs - n = 0 := by
  omega

theorem n08_sub_cancel (xs : List Nat) (n : Nat) : total xs + n - n = total xs := by
  omega

theorem n09_le_trans (xs : List Nat) (a b : Nat) (h : total xs ≤ a) (k : a ≤ b) : total xs ≤ b := by
  exact Nat.le_trans h k

theorem n10_peak_head (x : Nat) (xs : List Nat) : x ≤ peak (x :: xs) := by
  simp only [peak]; split <;> omega

theorem n11_peak_tail (x : Nat) (xs : List Nat) : peak xs ≤ peak (x :: xs) := by
  simp only [peak]; split <;> omega

theorem n12_power_one (n : Nat) : power 1 n = 1 := by
  induction n <;> simp [power, *]

theorem n13_power_zero (a : Nat) : power a 0 = 1 := by
  rfl

theorem n14_factorial_four  : factorial 4 = 24 := by
  decide

theorem n15_power_closed  : power 2 5 = 32 := by
  decide

theorem n16_itotal_cons (x : Int) (xs : List Int) : itotal (x :: xs) - x = itotal xs := by
  simp [itotal] <;> omega

theorem n17_int_cancel (xs : List Int) (n : Int) : itotal xs + n - n = itotal xs := by
  omega

theorem n18_int_bound (xs : List Int) (n : Int) (h : itotal xs ≤ n) : itotal xs - n ≤ 0 := by
  omega

theorem n19_simp_arith (xs : List Nat) : total xs + 1 ≠ 0 := by
  simp +arith

theorem n20_total_closed  : total [2, 3, 4] = 9 ∧ 3 - 5 = 0 := by
  decide
