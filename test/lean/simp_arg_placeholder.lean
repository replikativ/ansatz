-- Lean 4.33.1 Elab/Tactic/Simp.lean elabSimpTheorem: a simp argument's remaining
-- metavariables are abstracted (abstractMVars), so `_` makes the lemma general.
-- test/ansatz/tactic/simp_arg_placeholder_test.clj mirrors these.
example (n : Nat) : n + 0 = n := by simp only [Nat.add_zero _]
example (n m : Nat) : (n + 0) + (m + 0) = n + m := by simp only [Nat.add_zero _]
example (n : Nat) (h : n + 0 = 5) : n = 5 := by simp only [Nat.add_zero _] at h; exact h
example (n m : Nat) : n + m = m + n := by simp only [Nat.add_comm n _]
