import Lean
open Lean

-- Safe low-level MetavarContext cases. Assignment APIs intentionally do not
-- perform type checking; these test native Expr/context semantics, not proofs.
def mv (n : Name) : Expr := .mvar ⟨n⟩
def fv (n : Name) : Expr := .fvar ⟨n⟩
def atom : Expr := .sort .zero
def lam (e : Expr) : Expr := .lam .anonymous atom e .default
def put (m : MetavarContext) (n : Name) (e : Expr) : MetavarContext := assignExp m ⟨n⟩ e
def delay (m : MetavarContext) (n pending : Name) (xs : Array Expr) : MetavarContext :=
  { m with dAssignment := m.dAssignment.insert ⟨n⟩ { fvars := xs, mvarIdPending := ⟨pending⟩ } }
def has (m : MetavarContext) (n : Name) (e : Expr) : Bool :=
  m.getExprAssignmentExp ⟨n⟩ == some e
def domainSize (m : MetavarContext) : Nat := (MetavarContext.getExprAssignmentDomain m).size

def main : IO Unit := do
  let (m, e) := instantiateExprMVarsImp {} atom
  IO.println s!"closed:{e == atom && domainSize m == 0}"
  let (m, e) := instantiateExprMVarsImp {} (mv `unassigned)
  IO.println s!"bare:{e == mv `unassigned && domainSize m == 0}"
  let input := put (put {} `b atom) `a (mv `b)
  let (m, e) := instantiateExprMVarsImp input (mv `a)
  IO.println s!"direct-chain:{e == atom && has m `a atom && has m `b atom && domainSize m == 2}"
  let input := { ({} : MetavarContext) with lAssignment := ({} : PersistentHashMap LMVarId Level).insert ⟨`u⟩ (.succ .zero) }
  let (m, e) := instantiateExprMVarsImp input (.sort (.mvar ⟨`u⟩))
  IO.println s!"level:{e == .sort (.succ .zero) && getLevelMVarAssignmentExp m ⟨`u⟩ == some (.succ .zero) && domainSize m == 0}"
  let input := delay (put {} `p (fv `x)) `h `p #[fv `x]
  let (m, e) := instantiateExprMVarsImp input (.app (mv `h) (fv `actual))
  IO.println s!"exact:{e == fv `actual && has m `p (fv `x) && domainSize m == 1}"
  let input := delay (put {} `p (lam (.bvar 0))) `h `p #[]
  let (m, e) := instantiateExprMVarsImp input (.app (mv `h) (fv `actual))
  IO.println s!"zero-fvars-beta:{e == fv `actual && has m `p (lam (.bvar 0)) && domainSize m == 1}"
  let input := delay (put {} `p (lam (fv `x))) `h `p #[fv `x]
  let (m, e) := instantiateExprMVarsImp input (.app (mv `h) (.bvar 0))
  IO.println s!"binder-lift:{e == lam (.bvar 1) && has m `p (lam (fv `x)) && domainSize m == 1}"
  let input := delay (put {} `p (fv `x)) `h `p #[fv `x, fv `x]
  let (m, e) := instantiateExprMVarsImp input (.app (.app (mv `h) (fv `first)) (fv `last))
  IO.println s!"duplicate-fvars:{e == fv `last && has m `p (fv `x) && domainSize m == 1}"
  let input := delay (put {} `p atom) `h `p #[fv `x, fv `y]
  let source := .app (mv `h) atom
  let (m, e) := instantiateExprMVarsImp input source
  IO.println s!"too-few:{e == source && has m `p atom && domainSize m == 1}"
  let input := delay {} `h `p #[]
  let (m, e) := instantiateExprMVarsImp input source
  IO.println s!"unassigned-pending:{e == source && domainSize m == 0}"
  let input := delay (put {} `p (fv `y)) `inner `p #[fv `y]
  let input := put input `q (.app (mv `inner) (fv `x))
  let input := delay input `outer `q #[fv `x]
  let (m, e) := instantiateExprMVarsImp input (.app (mv `outer) (fv `actual))
  IO.println s!"nested:{e == fv `actual && has m `p (fv `y) && has m `q (.app (mv `inner) (fv `x)) && domainSize m == 2}"
  let input := delay (put {} `p (fv `resolved)) `good `p #[]
  let old := .app (.app (mv `good) atom) (mv `unassigned)
  let input := delay (put input `q old) `stuck `q #[]
  let source := .app (mv `stuck) atom
  let (m, e) := instantiateExprMVarsImp input source
  let updated := .app (.app (fv `resolved) atom) (mv `unassigned)
  IO.println s!"writeback:{e == source && has m `p (fv `resolved) && has m `q updated && domainSize m == 2}"
