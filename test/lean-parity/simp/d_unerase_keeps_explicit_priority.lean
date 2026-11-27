/-
Ansatz test: ansatz.tactic.simp-arg-modifiers-test/an-un-erased-origin-keeps-an-earlier-explicit-priority
Observed with Lean v4.36.0: inherited `↓ h` at 100 masked by `← h`, inherited `↓ k` at 500: `simp [↓ h, -h, h]` gives `G x`; `simp [h]` gives `K x`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque P : Nat → Prop
opaque F : Nat → Nat
opaque G : Nat → Nat
opaque K : Nat → Nat
opaque x : Nat
axiom h : F x = G x
axiom k : F x = K x
attribute [simp ↓ 100] h
attribute [simp ← 100] h
attribute [simp ↓ 500] k

example (hp : P (G x)) : P (F x) := by simp [↓ h, -h, h]; exact hp
example (hp : P (K x)) : P (F x) := by simp [h]; exact hp
