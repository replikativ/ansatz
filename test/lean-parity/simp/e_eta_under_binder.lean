/-
Ansatz test: ansatz.tactic.simp-pre-test/eta-matching-under-an-enclosing-binder
Observed with Lean v4.36.0: `q2 : Q2 (fun x => K2 (F2 x))` closes `Q2 (fun x => K2 (fun y => F2 x y))`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque F2 : Nat → Nat → Nat
opaque K2 : (Nat → Nat) → Nat
opaque Q2 : (Nat → Nat) → Prop
axiom q2 : Q2 (fun x => K2 (F2 x))

example : Q2 (fun x => K2 (fun y => F2 x y)) := by simp only [q2]
