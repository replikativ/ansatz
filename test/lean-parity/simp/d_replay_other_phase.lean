/-
Ansatz test: ansatz.companion-overlay-test/reactivating-over-a-base-with-another-phase-keeps-the-live-inverse
Observed with Lean v4.36.0: after `[simp ↓] n`, `[simp] n`, `[simp ←] n` only `← n` is live.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque P : Nat → Prop
opaque F : Nat → Nat
opaque A : Nat
opaque B : Nat
axiom n : F A = F B
attribute [simp ↓] n
attribute [simp] n
attribute [simp ←] n

example (hp : P (F A)) : P (F B) := by simp; exact hp
