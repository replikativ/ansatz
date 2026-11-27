/-
Ansatz test: ansatz.tactic.simp-pre-test/nat-literal-disequality-is-nat-reduceEqDiff
Observed with Lean v4.36.0: `reduceCtorEq` leaves `1 = 2` alone (two Nat.succ constructors).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
example (h : (1 : Nat) = 2) : True := by
  fail_if_success simp only [reduceCtorEq] at h
  trivial
