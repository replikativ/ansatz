/-
Ansatz test: ansatz.tactic.simp-inverse-test/inverse-bad-rewrite-check-unfolds-through-metadata
Observed with Lean v4.36.0: the inverse of `∀ x, idM x = x` with a reducible `idM := fun x => x` is rejected (the surface cannot place metadata in the body; Lean's betaRev looks through it, so the outcome is the same).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
@[reducible] def idM : Nat → Nat := fun x => x
theorem idM_eq : ∀ x, idM x = x := fun _ => rfl

/--
error: Invalid simp theorem: Equation is equivalent to
  x = x
-/
#guard_msgs in
example (y : Nat) : y = y := by simp only [← idM_eq]
