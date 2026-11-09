/-
Lean v4.33.1 reference for test/ansatz/tactic/sorry_test.clj.
Run: lean test/lean/sorry.lean  (no output means every #guard_msgs matched)
-/

-- The `sorry` tactic closes the goal and the declaration warns.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem sorry_closes : 1 = 2 := by sorry

-- `admit` is a synonym.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem admit_closes : 1 = 2 := by admit

-- A term `sorry`, at any type.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem term_sorry (n : Nat) : n + 0 = n := by exact sorry

-- Each `sorry` is unique: two are not definitionally equal.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem unique_sorries : (sorry : Nat) = sorry := by
  fail_if_success rfl
  sorry

-- The axiom behind it.
/-- info: 'sorry_closes' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms sorry_closes
