/-
Ansatz test: ansatz.tactic.simp-inverse-test/inverse-bad-rewrite-check-has-a-step-limit
Observed with Lean v4.36.0: the inverse of `∀ x, d12 x = x` (reducible d(i+1) x := di (di x), d0 x := x, 2^13 unfoldings) is rejected as `x = x` in well under a second; Lean has no step limit (d40 runs for minutes).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
@[reducible] def d0 : Nat → Nat := fun x => x
@[reducible] def d1 : Nat → Nat := fun x => d0 (d0 x)
@[reducible] def d2 : Nat → Nat := fun x => d1 (d1 x)
@[reducible] def d3 : Nat → Nat := fun x => d2 (d2 x)
@[reducible] def d4 : Nat → Nat := fun x => d3 (d3 x)
@[reducible] def d5 : Nat → Nat := fun x => d4 (d4 x)
@[reducible] def d6 : Nat → Nat := fun x => d5 (d5 x)
@[reducible] def d7 : Nat → Nat := fun x => d6 (d6 x)
@[reducible] def d8 : Nat → Nat := fun x => d7 (d7 x)
@[reducible] def d9 : Nat → Nat := fun x => d8 (d8 x)
@[reducible] def d10 : Nat → Nat := fun x => d9 (d9 x)
@[reducible] def d11 : Nat → Nat := fun x => d10 (d10 x)
@[reducible] def d12 : Nat → Nat := fun x => d11 (d11 x)

axiom dchain : ∀ x, d12 x = x

/--
error: Invalid simp theorem: Equation is equivalent to
  x = x
-/
#guard_msgs in
example (y : Nat) : y = y := by simp only [← dchain]
