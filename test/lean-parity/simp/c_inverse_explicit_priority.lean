/-
Ansatz test: ansatz.tactic.simp-arg-modifiers-test/bare-and-parenthesized-inverses-take-the-explicit-priority
Observed with Lean v4.36.0: with `@[simp 100] t : a = b` and `@[simp 500] s2 : b = c`, both `simp [← t]` and `simp [← (t)]` rewrite `P b` to `P a`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque P : Nat → Prop
opaque a : Nat
opaque b : Nat
opaque c : Nat
@[simp 100] axiom t : a = b
@[simp 500] axiom s2 : b = c

example (h : P a) : P b := by simp [← t]; exact h
example (h : P a) : P b := by simp [← (t)]; exact h
