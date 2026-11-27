/-
Ansatz test: ansatz.tactic.simp-arg-modifiers-test/a-prop-domain-that-simplifies-goes-through-forall-prop-domain-congr
Observed with Lean v4.36.0: `simp` closes `∀ h : n.succ = 0, Q h` (simpForall's forall_prop_domain_congr).
-/
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
example (n : Nat) (Q : n.succ = 0 → Prop) : ∀ h : n.succ = 0, Q h := by simp
