import Lean

/- Original native quick sharing over unambiguous source-produced values.
   Pointer observations are equality booleans only, never numeric addresses.
   Target-only scalar/extent/capacity choices are deliberately not oracle claims. -/
@[noinline] def mkList (n : Nat) : List Nat := [n, n + 1]
@[noinline] def mkExpr (n : Nat) : Lean.Expr := .app (.bvar n) (.bvar (n + 1))

unsafe def main : IO Unit := do
  let r ← IO.mkRef (7 : Nat)
  let n₁ ← r.get
  let n₂ ← r.get
  let a := mkList n₁
  let b := mkList n₂
  let input := (a, b)
  let output := ShareCommon.shareCommon' input
  IO.println s!"list-content: {output.1 == [7, 8] && output.2 == [7, 8]}"
  IO.println s!"list-shared: {ptrEq output.1 output.2}"
  let e₁ := mkExpr n₁
  let e₂ := mkExpr n₂
  let exprs := ShareCommon.shareCommon' (e₁, e₂)
  IO.println s!"expr-shared: {ptrEq exprs.1 exprs.2}"
  let dag := ShareCommon.shareCommon' (a, a)
  IO.println s!"dag-shared: {ptrEq dag.1 dag.2}"
  let array := ShareCommon.shareCommon' (#[n₁, n₁ + 1], #[n₂, n₂ + 1])
  IO.println s!"array-shared: {ptrEq array.1 array.2}"
  let opaquePair := ShareCommon.shareCommon' (r, r)
  IO.println s!"opaque-ref: {ptrEq opaquePair.1 r && ptrEq opaquePair.1 opaquePair.2}"
