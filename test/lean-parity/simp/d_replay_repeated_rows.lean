/-
Ansatz test: ansatz.companion-overlay-test/reactivating-a-repeated-row-keeps-the-live-inverse (the replayed state: attrs/import-attr-tuples)
Observed with Lean v4.36.0: after `attribute [simp] n`, `attribute [simp] n`, `attribute [simp ←] n` only `← n` is live.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque P : Nat → Prop
opaque A : Nat
opaque B : Nat
axiom n : A = B
attribute [simp] n
attribute [simp] n
attribute [simp ←] n

example (hp : P A) : P B := by simp; exact hp
