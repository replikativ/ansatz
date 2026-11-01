import Lean

open Lean
namespace ExprMVarsProbe

private def nm (s : String) : Name := .str .anonymous s
private def mv (s : String) : Expr := mkMVar ⟨nm s⟩
private def fv (s : String) : Expr := mkFVar ⟨nm s⟩
private def c (s : String) : Expr := mkConst (nm s)

/-- Real PersistentHashMap direct-assignment lookup and normalization writeback. -/
@[noinline] def directSummary (seed : Nat) : Nat := Id.run do
  let a := c "A"
  let before := assignExp (assignExp {} ⟨nm "n"⟩ a) ⟨nm "m"⟩ (mv "n")
  let (after, output) := instantiateExprMVarsImp before (mv "m")
  return seed + (if output == a then 1 else 0) +
    (if after.eAssignment.find? ⟨nm "m"⟩ == some a then 10 else 0)

/-- The pending declaration keeps its original local context, while the result
substitutes an open bvar through a binder and lifts it to avoid capture. -/
@[noinline] def delayedSummary (seed : Nat) : Nat := Id.run do
  let x := fv "x"
  let pending := mkLambda (nm "y") .default (mkSort .zero) x
  let before := assignExp {} ⟨nm "p"⟩ pending
  let delayed : DelayedMetavarAssignment := {fvars := #[x], mvarIdPending := ⟨nm "p"⟩}
  let before := {before with dAssignment := before.dAssignment.insert ⟨nm "d"⟩ delayed}
  let (after, output) := instantiateExprMVarsImp before (mkApp (mv "d") (mkBVar 0))
  let expected := mkLambda (nm "y") .default (mkSort .zero) (mkBVar 1)
  return seed + (if output == expected then 1 else 0) +
    (if after.eAssignment.find? ⟨nm "p"⟩ == some pending then 10 else 0)

/-- A nonresolvable outer delayed assignment remains in the expression while
its pending value receives normalized, resolvable inner assignments. -/
@[noinline] def cutSummary (seed : Nat) : Nat := Id.run do
  let x := fv "x"
  let y := fv "y"
  let pending := mkApp2 (c "Pair") (mkApp (mv "e") (c "A")) (mv "unknown")
  let before := assignExp (assignExp {} ⟨nm "p"⟩ pending) ⟨nm "q"⟩ y
  let delayed : DelayedMetavarAssignment := {fvars := #[x], mvarIdPending := ⟨nm "p"⟩}
  let inner : DelayedMetavarAssignment := {fvars := #[y], mvarIdPending := ⟨nm "q"⟩}
  let da := (before.dAssignment.insert ⟨nm "d"⟩ delayed).insert ⟨nm "e"⟩ inner
  let before := {before with dAssignment := da}
  let input := mkApp (mv "d") (c "B")
  let (after, output) := instantiateExprMVarsImp before input
  let expectedPending := mkApp2 (c "Pair") (c "A") (mv "unknown")
  return seed + (if output == input then 1 else 0) +
    (if after.eAssignment.find? ⟨nm "p"⟩ == some expectedPending then 10 else 0) +
    (if after.eAssignment.find? ⟨nm "q"⟩ == some y then 100 else 0)

end ExprMVarsProbe
