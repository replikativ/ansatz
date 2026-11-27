/-
Ansatz test: ansatz.tactic.simp-inverse-test/inverse-of-a-non-theorem-or-a-bad-rewrite-is-rejected (strict eta)
Observed with Lean v4.36.0: `simp [← eta_refl]` is rejected: checkBadRewrite eta-reduces `fun x => f x` to `f`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem eta_refl : ∀ f : Nat → Nat, (fun x => f x) = f := fun _ => rfl

/--
error: Invalid simp theorem: Equation is equivalent to
  f = f
-/
#guard_msgs in
example (g : Nat → Nat) : g = g := by simp [← eta_refl]
