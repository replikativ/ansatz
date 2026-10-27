import Lean

-- Lean references for the simp/decide unit regressions; no Mathlib.
example (a b : Nat) : a + b = b + a := by simp only [Nat.add_comm]
example (b : Bool) (x : Nat) : Bool.rec (motive := fun _ => Nat) x x b = x := by cases b <;> rfl
example (x : Nat) : x < Nat.add x 1 := by simp
example (p : Prop) (x y : Nat) (h : x = y) (ih : p → x = 0) : p → y = 0 := by simp_all
example (n : Nat) [Decidable (n = n)] : n = n := by
  fail_if_success decide
  rfl
example : (∀ n : Nat, n = n) = True := by simp

namespace SimpDecide
axiom closedGoal : Prop

-- Elab/Tactic/Decide.lean preprocessPropToDecide accepts the closed type;
-- evalDecideCore/mkDecideProof selects the local instance, which stays opaque.
example [_d : Decidable closedGoal] (h : closedGoal) : closedGoal := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let prop := Lean.mkConst ``closedGoal
    unless !prop.hasFVar do throwError "expected a closed proposition"
    let pf ← Lean.Meta.mkDecideProof prop
    let inst := pf.appFn!.appArg!
    let localDecl ← Lean.Meta.getLocalDeclFromUserName `_d
    unless inst == localDecl.toExpr do throwError "expected the local Decidable instance"
    let reduced ← Lean.Meta.whnf inst
    unless reduced == inst do throwError "expected an opaque local instance"
  fail_if_success decide
  exact h
end SimpDecide
