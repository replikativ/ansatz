/-
Ansatz test: ansatz.tactic.simp-pre-test/eta-matching-binds-a-rule-parameter
Observed with Lean v4.36.0: `h3 : ∀ n, R3 (F3 n) = n` rewrites `R3 (fun x => F3 a x)` to `a`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque F3 : Nat → Nat → Nat
opaque R3 : (Nat → Nat) → Nat
opaque a : Nat
axiom h3 : ∀ n : Nat, R3 (F3 n) = n

example : R3 (fun x => F3 a x) = a := by simp only [h3]
