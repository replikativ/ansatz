import Lean
open Lean

-- Safe regular cases only. Never execute the continued s32<d32 assertion domain.
-- Identity observations are booleans, not pointer words or a physical-layout claim.
unsafe def main : IO Unit := do
  let ref ← IO.mkRef (3 : Nat)
  let n ← ref.get
  let input := Expr.bvar (n + 2)
  let partialApp := Expr.app (.bvar 0) (.bvar 2)
  IO.println s!"partial:{partialApp.hasLooseBVar 0 && !partialApp.hasLooseBVar 1 && partialApp.hasLooseBVar 2}"
  let binder := Expr.lam .anonymous (.sort .zero) (.bvar 1) .default
  IO.println s!"binder:{binder.hasLooseBVar 0 && !binder.hasLooseBVar 1}"
  let binding := Expr.letE .anonymous (.sort .zero) (.bvar 0) (.bvar 3) true
  IO.println s!"let-offset:{binding.hasLooseBVar 0 && binding.hasLooseBVar 2 && !binding.hasLooseBVar 1}"
  IO.println s!"wrap-zero:{(Expr.bvar 0).hasLooseBVar (2^32)}"
  IO.println s!"wrap-one:{(Expr.bvar 1).hasLooseBVar (2^32+1)}"
  IO.println s!"heap-query:{!input.hasLooseBVar (2^80)}"
  let shared := Expr.bvar 1
  let sharedTree := Expr.app (.lam .anonymous (.sort .zero) shared .default) shared
  IO.println s!"shared-offsets:{sharedTree.hasLooseBVar 0 && sharedTree.hasLooseBVar 1 && !sharedTree.hasLooseBVar 2}"
  IO.println s!"lower-basic:{input.lowerLooseBVars n 2 == .bvar n}"
  IO.println s!"lower-cutoff:{ptrEq input (input.lowerLooseBVars (n+3) 2)}"
  IO.println s!"lower-zero:{ptrEq input (input.lowerLooseBVars 0 0)}"
  IO.println s!"lower-full-compare:{ptrEq input (input.lowerLooseBVars 1 (2^32+1))}"
  IO.println s!"lower-heap-s:{ptrEq input (input.lowerLooseBVars (2^80) 1)}"
  IO.println s!"lower-heap-d:{ptrEq input (input.lowerLooseBVars 0 (2^80))}"
  IO.println s!"lower-wrap:{input.lowerLooseBVars (2^32+2) (2^32+1) == .bvar (n+1)}"
  IO.println s!"lower-wrap-zero:{ptrEq input (input.lowerLooseBVars (2^32) (2^32))}"
  let closed := Expr.sort .zero
  IO.println s!"lower-closed-shortcut:{ptrEq closed (closed.lowerLooseBVars (2^32) 1)}"
  let under := Expr.lam .anonymous (.sort .zero) (.app (.bvar 0) (.bvar 4)) .default
  IO.println s!"lower-binder:{under.lowerLooseBVars 3 2 == .lam .anonymous (.sort .zero) (.app (.bvar 0) (.bvar 2)) .default}"
