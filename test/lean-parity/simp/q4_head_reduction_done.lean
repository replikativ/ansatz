/-
Ansatz test: ansatz.tactic.simp-pre-test/a-terminal-result-of-a-head-reduction-is-not-revisited
Observed with Lean v4.36.0: `(fun _ => true = false) 0` becomes `False`; the post rule `False = Q` does not run on it.
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
opaque Q : Prop
axiom fq : False = Q

-- h becomes False (closing the goal); had fq run, h : Q would leave the goal open
example (h : (fun _ : Nat => true = false) 0) : False := by simp only [↓ reduceCtorEq, fq] at h
