import Lean
open Lean

/- Safe, source-produced cases only. Fatal range/result panic cases are excluded.
   Pointer observations are booleans, never addresses. Root may run pinned Lean;
   this prepared source is not a worker execution or an AOT claim. -/
unsafe def main : IO Unit := do
  let r ← IO.mkRef (7 : Nat)
  let n ← r.get
  let e := Expr.app (.bvar 0) (.bvar 1)
  let values := #[Expr.bvar (n + 3), Expr.bvar (n + 13)]
  IO.println s!"forward: {e.instantiate values == .app (.bvar 10) (.bvar 20)}"
  IO.println s!"reverse: {e.instantiateRev values == .app (.bvar 20) (.bvar 10)}"
  IO.println s!"single: {e.instantiate1 (.bvar 10) == .app (.bvar 10) (.bvar 0)}"
  let larger := #[Expr.bvar 99, Expr.bvar 10, Expr.bvar 20, Expr.bvar 98]
  IO.println s!"range: {e.instantiateRange 1 3 larger == .app (.bvar 10) (.bvar 20)}"
  IO.println s!"reverse-range: {e.instantiateRevRange 1 3 larger == .app (.bvar 20) (.bvar 10)}"
  let binder := Expr.lam .anonymous (.sort .zero) (.app (.bvar 0) (.bvar 1)) .default
  IO.println s!"binder-lift: {binder.instantiate1 (.bvar 2) == .lam .anonymous (.sort .zero) (.app (.bvar 0) (.bvar 3)) .default}"
  IO.println s!"forward-empty-identity: {ptrEq e (e.instantiate #[])}"
  let reverseEmpty := e.instantiateRev #[]
  IO.println s!"reverse-empty-content: {reverseEmpty == e}"
  IO.println s!"reverse-empty-rebuild: {!ptrEq e reverseEmpty}"
  IO.println s!"forward-empty-range-identity: {ptrEq e (e.instantiateRange 1 1 larger)}"
  IO.println s!"reverse-empty-range-rebuild: {!ptrEq e (e.instantiateRevRange 1 1 larger)}"
  let closed := Expr.sort .zero
  IO.println s!"reverse-empty-closed-identity: {ptrEq closed (closed.instantiateRev #[])}"
  IO.println s!"lift: {e.liftLooseBVars 0 2 == .app (.bvar 2) (.bvar 3)}"
  IO.println s!"cutoff: {e.liftLooseBVars 1 2 == .app (.bvar 0) (.bvar 3)}"
  let modulus : Nat := 2^32
  IO.println s!"scalar-cutoff-wrap: {e.liftLooseBVars modulus 1 == .app (.bvar 1) (.bvar 2)}"
  IO.println s!"scalar-delta-wrap-identity: {ptrEq e (e.liftLooseBVars 0 modulus)}"
  let heapNat : Nat := 2^63
  IO.println s!"heap-cutoff-identity: {ptrEq e (e.liftLooseBVars heapNat 1)}"
  IO.println s!"heap-delta-identity: {ptrEq e (e.liftLooseBVars 0 heapNat)}"
  let near := Expr.bvar 1048573
  IO.println s!"largest-valid-result: {near.liftLooseBVars 0 1 == .bvar 1048574}"
