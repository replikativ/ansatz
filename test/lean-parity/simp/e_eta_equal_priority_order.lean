/-
Ansatz test: ansatz.tactic.simp-pre-test/equal-priority-eta-spellings-keep-their-insertion-order
Observed with Lean v4.36.0: pre rules `R (fun x => F x) = 0`, `R F = s`, `s = R (fun x => F x)` at one priority: `[↓ rl, ↓ rf, ↓ sr]` ends at `0`; `[↓ rf, ↓ rl, ↓ sr]` loops (both lhs share the eta key).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque F : Nat → Nat
opaque R : (Nat → Nat) → Nat
opaque s : Nat
opaque P : Nat → Prop
axiom rl : R (fun x => F x) = 0
axiom rf : R F = s
axiom sr : s = R (fun x => F x)

example (hp : P 0) : P (R (fun x => F x)) := by simp only [↓ rl, ↓ rf, ↓ sr]; exact hp

-- rf first: R L → s → R L … never reaches 0 (here: a step bound instead of the recursion limit)
example (hp : P 0) : P (R (fun x => F x)) := by
  fail_if_success simp (maxSteps := 200) only [↓ rf, ↓ rl, ↓ sr]
  rw [rl]; exact hp
