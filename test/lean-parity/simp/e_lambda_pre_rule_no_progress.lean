/-
Ansatz test: ansatz.tactic.simp-pre-test/a-lambda-keyed-pre-rule-is-judged-against-the-original-term
Observed with Lean v4.36.0: `simp only [↓ h_lam]` on `P (R (fun x => F x))` makes no progress (the rhs is the term itself).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque F : Nat → Nat
opaque R : (Nat → Nat) → Nat
opaque P : Nat → Prop
axiom h_lam : R (fun x => (fun z => z) (F x)) = R (fun x => F x)

/-- error: `simp` made no progress -/
#guard_msgs in
example : P (R (fun x => F x)) := by simp only [↓ h_lam]
