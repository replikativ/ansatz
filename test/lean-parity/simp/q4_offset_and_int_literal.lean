/-
Ansatz test: ansatz.tactic.simp-pre-test/the-constructor-probe-recognizes-offsets-and-int-literals
Observed with Lean v4.36.0: `F x + (0 + 1) = 0` (as Nat.add) closes before `grow` loops; `-1 = Int.ofNat n` closes.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque F : Nat → Nat
opaque S : Nat → Nat
axiom grow : ∀ n, F n = F (S n)

example (x : Nat) (h : Nat.add (F x) (Nat.add 0 1) = 0) : False := by
  simp only [↓ reduceCtorEq, grow] at h
example (n : Nat) (h : (-1 : Int) = Int.ofNat n) : False := by simp only [reduceCtorEq] at h
