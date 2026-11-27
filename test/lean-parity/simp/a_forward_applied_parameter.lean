/-
Ansatz test: ansatz.tactic.simp-inverse-test/forward-rule-with-an-applied-parameter-waits-for-its-arguments
Observed with Lean v4.36.0: `R g (g a)` simplifies to `R g (g b)`: `a = b` rewrites first, `hR` never fires.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque R : (Nat → Nat) → Nat → Nat
opaque W : Nat → Nat
opaque a : Nat
opaque b : Nat
opaque g : Nat → Nat
axiom hR : ∀ f : Nat → Nat, R f (f a) = W (R f (f a))
axiom jab : a = b

example : R g (g a) = R g (g b) := by simp only [hR, jab]
