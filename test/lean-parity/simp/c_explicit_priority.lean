/-
Ansatz test: ansatz.tactic.simp-arg-modifiers-test/a-parenthesized-constant-takes-the-explicit-priority
Observed with Lean v4.36.0: with `@[simp 100] t : a = b` and `@[simp 500] s : a = c`, `simp` gives `P c`; `simp [(t)]` and `simp [t]` give `P b` (explicit priority 1000).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque P : Nat → Prop
opaque a : Nat
opaque b : Nat
opaque c : Nat
@[simp 100] axiom t : a = b
@[simp 500] axiom s : a = c

example (h : P c) : P a := by simp; exact h
example (h : P b) : P a := by simp [(t)]; exact h
example (h : P b) : P a := by simp [t]; exact h
