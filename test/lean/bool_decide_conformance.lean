-- Reference for ansatz.bool-decide-conformance-test; Lean 4.33.1, Init only.
-- Bool laws use Init/Data/Bool.lean; decide follows
-- Lean/Elab/Tactic/Decide.lean evalDecideCore (comparison goals become closed after subst).
def ready (a b : Bool) : Bool := a && !b
def allowed (a b : Bool) : Bool := a || b
def low (x y : Nat) : Nat := if x ≤ y then x else y
def same (x y : Nat) : Bool := if x == y then true else false
def bleLow (x y : Nat) : Nat := if Nat.ble x y then x else y

theorem b01_ready_false (a : Bool) : ready a false = a := by simp [ready]
theorem b02_ready_true (a : Bool) : ready a true = false := by simp [ready]
theorem b03_allowed_false (a : Bool) : allowed a false = a := by simp [allowed]
theorem b04_allowed_true (a : Bool) : allowed a true = true := by simp [allowed]
theorem b05_ready_idem (a b : Bool) : ready (ready a b) b = ready a b := by
  cases a <;> cases b <;> simp [ready]
theorem b06_allowed_comm (a b : Bool) : allowed a b = allowed b a := by
  cases a <;> cases b <;> simp [allowed]
theorem b07_demorgan (a b : Bool) : !(allowed a b) = (!a && !b) := by
  cases a <;> cases b <;> simp [allowed]
theorem b08_double_not (a b : Bool) : !(!(ready a b)) = ready a b := by simp
theorem b09_and_true (a b : Bool) (h : (a && b) = true) : a = true := by
  simp [Bool.and_eq_true] at h
  exact h.1
theorem b10_ready_hyp (a b : Bool) (h : ready a b = true) : a = true := by
  cases a <;> cases b <;> simp_all [ready]
theorem b11_or_false (a b : Bool) : allowed a b = false → a = false := by
  cases a <;> cases b <;> simp [allowed]
theorem b12_low_refl (x : Nat) : low x x = x := by simp [low]
theorem b13_low_of_le (x y : Nat) (h : x ≤ y) : low x y = x := by simp [low, h]
theorem b14_low_of_gt (x y : Nat) (h : y < x) : low x y = y := by
  have hnot : ¬ x ≤ y := by omega
  simp [low, hnot]
theorem b15_bleLow_refl (x : Nat) : bleLow x x = x := by simp [bleLow]
theorem b16_ble_bridge (x y : Nat) (h : x ≤ y) : Nat.ble x y = true := by
  simp [Nat.ble_eq, h]
theorem b17_beq_bridge (x y : Nat) (h : x = y) : same x y = true := by simp [same, h]
theorem b18_beq_refl (x : Nat) : same x x = true := by simp [same]
theorem b19_closed_le : 3 ≤ 7 := by decide
theorem b20_closed_not_le : ¬ (7 ≤ 3) := by decide
theorem b21_closed_code : low 9 4 = 4 ∧ same 3 3 = true := by decide
theorem b22_decide_subst (x y : Nat) (hx : x = 3) (hy : y = 7) : x ≤ y := by
  subst hx
  subst hy
  decide
theorem b23_decide_subst_zero (x : Nat) (hx : x = 0) : x ≤ 5 := by
  subst hx
  decide
theorem b24_cases_comparison (x y : Nat) : bleLow x y = x ∨ bleLow x y = y := by
  cases h : Nat.ble x y <;> simp [bleLow, h]
theorem b25_prop_bool (x y : Nat) (h : Nat.ble x y = true) : x ≤ y := by
  simp [Nat.ble_eq] at h
  exact h
