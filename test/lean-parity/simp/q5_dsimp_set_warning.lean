/-
Ansatz test: ansatz.tactic.simp-arg-modifiers-test/dsimp-keeps-its-erase-warning-with-a-pre-simproc-set
Observed with Lean v4.36.0: `dsimp [s, -Nat.pred_le] at h` (s with `↓ Nat.reduceAdd`) closes `False` and warns once.
-/
import ParitySimpSets
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [parity_dpre_set ↓] Nat.reduceAdd

/-- warning: `Nat.pred_le` does not have the `[simp]` attribute -/
#guard_msgs in
example (P : Prop) (h : False) : P := by dsimp [parity_dpre_set, -Nat.pred_le] at h
