/-
Ansatz test: ansatz.tactic.simp-arg-modifiers-test/a-later-erasure-disables-a-sets-pre-simproc
Observed with Lean v4.36.0: a set with `↓ Nat.reduceAdd` and `f_ax`: `simp only [s, -Nat.reduceAdd]` and `simp only [-Nat.reduceAdd, s]` both close `f x x = x` (Ansatz refuses the live order only for a `↓` simproc it has not ported).
-/
import ParitySimpSets
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

opaque f : Nat → Nat → Nat
axiom f_ax : ∀ x, f x x = x
attribute [parity_pre_set ↓] Nat.reduceAdd
attribute [parity_pre_set] f_ax

example (x : Nat) : f x x = x := by simp only [parity_pre_set, -Nat.reduceAdd]
example (x : Nat) : f x x = x := by simp only [-Nat.reduceAdd, parity_pre_set]
