/-
Ansatz test: ansatz.tactic.simp-inverse-test/inverse-rule-with-an-applied-parameter-is-indexed
Observed with Lean v4.36.0: `simp only [← sr]` rewrites `R g (g a)` to `S g`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque R : (Nat → Nat) → Nat → Nat
opaque S : (Nat → Nat) → Nat
opaque a : Nat
opaque g : Nat → Nat
axiom sr : ∀ f : Nat → Nat, S f = R f (f a)

example : R g (g a) = S g := by simp only [← sr]
