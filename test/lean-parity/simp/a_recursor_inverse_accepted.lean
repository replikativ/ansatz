/-
Ansatz test: ansatz.tactic.simp-inverse-test/inverse-bad-rewrite-check-does-not-reduce-recursors
Observed with Lean v4.36.0: the inverse of `∀ x, Bool.rec x x false = x` is accepted (simpGlobalConfig: iota := false).
-/
import Lean
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Lean Meta

theorem rec_refl : ∀ x : Nat, (@Bool.rec (fun _ => Nat) x x false) = x := fun _ => rfl

-- addConst runs preprocess and checkBadRewrite; it throws on a rejected theorem
run_meta do
  let _ ← ({} : SimpTheorems).addConst ``rec_refl (inv := true)
