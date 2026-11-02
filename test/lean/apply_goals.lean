import Lean

open Lean Meta Elab Tactic

-- Assert the binder tags returned by Meta.apply in goal order.
elab "check_apply" term:term:max mode:ident "[" tags:str,* "]" : tactic => do
  let e ← elabTermForApply term (mayPostpone := false)
  let mode := match mode.getId with
    | `all => ApplyNewGoals.all
    | `only => ApplyNewGoals.nonDependentOnly
    | _ => ApplyNewGoals.nonDependentFirst
  let expected := tags.getElems.toList.map (·.getString)
  let goals ← (← getMainGoal).apply e { newGoals := mode }
  let actual ← goals.mapM fun g => return (← g.getTag).eraseMacroScopes.toString
  unless actual == expected do throwError "unexpected goals: {actual}"
  replaceMainGoal goals

inductive Pack : Prop where
  | mk (ty : Type) (x : ty) (hx : x = x) (ht : True) : Pack

example : Pack := by
  check_apply Pack.mk default ["hx", "ht", "ty", "x"]
  case hx => exact Eq.refl (0 : Nat)
  case ht => trivial

example : Pack := by
  check_apply Pack.mk all ["ty", "x", "hx", "ht"]
  exact Nat
  exact 0
  rfl
  trivial

example : Pack := by
  check_apply Pack.mk only ["hx", "ht"]
  exact Eq.refl (0 : Nat)
  trivial

example (hf : False) (f : (ha : True) → (hb : False) → True) : True := by
  check_apply f default ["ha", "hb"]
  trivial
  exact hf

example (f : {n : Nat} → (h : n = 0) → True) : True := by
  check_apply f default ["h", "n"]
  exact Eq.refl 0

-- The elaborator synthesizes the instance in the head before Meta.apply;
-- the single remaining telescope hole inherits the anonymous parent tag.
example (f : ∀ [_inst : Inhabited Nat], (h : True) → True) : True := by
  check_apply (@f) default ["[anonymous]"]
  trivial

example (f : (True → True) → True → True) : True := by
  apply f _
  · trivial
  · intro h; exact h

example (n : Nat)
    (_bad : ∀ x : Nat, n = x → Nat.succ n = 0 → False)
    (good : ∀ x : Nat, n = x → False) : False := by
  first
  | apply _bad <;> rfl
  | apply good <;> rfl
