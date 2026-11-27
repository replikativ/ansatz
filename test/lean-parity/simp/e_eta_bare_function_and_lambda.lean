/-
Ansatz test: ansatz.tactic.simp-pre-test/rules-on-a-bare-function-match-its-eta-expansion and rules-indexed-under-a-lambda-stay-reachable
Observed with Lean v4.36.0: `Q F` and `Q (fun x => F x)` each close `Q (fun x => F x)`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque F : Nat → Nat
opaque Q : (Nat → Nat) → Prop
axiom q_fn : Q F
axiom q_lam : Q (fun x => F x)

example : Q (fun x => F x) := by simp only [q_fn]
example : Q (fun x => F x) := by simp only [q_lam]
