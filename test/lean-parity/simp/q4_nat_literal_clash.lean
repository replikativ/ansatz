/-
Ansatz test: ansatz.tactic.simp-pre-test/a-nat-constructor-clash-needs-no-ctor-idx and reduce-ctor-eq-sees-the-constructors-of-nat-literals
Observed with Lean v4.36.0: `simp only [reduceCtorEq] at h` closes `h : 0 = 1`.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
example (h : 0 = 1) : False := by simp only [reduceCtorEq] at h
