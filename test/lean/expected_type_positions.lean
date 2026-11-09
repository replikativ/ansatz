-- Lean 4.33.1: a nested match takes the type its position expects, not the enclosing
-- match's; a numeral's type may come from the goal `apply` unifies with
-- (Elab/Tactic/ElabTerm.lean evalApplyLikeTactic: elaborate postponing default instances,
-- apply, then synthesizeSyntheticMVarsNoPostponing).
-- test/ansatz/elab_expected_type_test.clj mirrors these. Check with
--   lean +leanprover/lean4:v4.33.1 test/lean/expected_type_positions.lean

def pick (o : Option Bool) (u e : Nat) : Option Nat :=
  match o with
  | some v => Option.some (match v with | true => u | false => e)
  | none => Option.none
example : pick (some true) 5 7 = some 5 := by decide
example : pick (some false) 5 7 = some 7 := by decide
example : pick none 5 7 = none := by decide

def keep (o : Option Bool) (u : Nat) : Option Nat :=
  match o with
  | some v => match v with | true => Option.some u | false => Option.none
  | none => Option.none
example : keep (some true) 4 = some 4 := by decide
example : keep (some false) 4 = none := by decide

example : ∃ n : Nat, n = n := by apply (Exists.intro 0); rfl
example : ∃ n : Int, n = n := by apply (Exists.intro 0); rfl
example : ∃ n : Int, n = 3 := by apply (Exists.intro 3); rfl
