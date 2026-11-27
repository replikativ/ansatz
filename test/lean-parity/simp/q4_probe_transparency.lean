/-
Ansatz test: ansatz.tactic.simp-pre-test/the-constructor-probe-runs-at-reducible-and-instances-transparency
Observed with Lean v4.36.0: `0 = one` with `def one := 1` is left alone; `0 = one'` with `abbrev one' := 1` becomes False.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
def one : Nat := 1
abbrev one' : Nat := 1

-- unchanged: simp at h makes no progress
example (h : 0 = one) : True := by
  fail_if_success simp only [↓ reduceCtorEq] at h
  trivial
example (h : 0 = one') : False := by simp only [↓ reduceCtorEq] at h
