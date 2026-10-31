import Lean
open Lean

/- Original native abstraction observations over ordinary source-produced Exprs.
   Small heap Nat, malformed caches and host metadata tampering are JVM models. -/
unsafe def main : IO Unit := do
  let x := Expr.fvar ⟨`x⟩
  let x₂ := Expr.fvar ⟨`x⟩
  let y := Expr.fvar ⟨`y⟩
  let mx := Expr.mvar ⟨`x⟩
  let term := mkApp x y
  IO.println s!"two-vars: {term.abstractRange 2 #[x₂, y] == mkApp (mkBVar 1) (mkBVar 0)}"
  IO.println s!"one-prefix: {term.abstractRange 1 #[x₂, y] == mkApp (mkBVar 0) y}"
  IO.println s!"zero-prefix: {ptrEq (term.abstractRange 0 #[x₂, y]) term}"
  IO.println s!"clamped-prefix: {term.abstractRange 99 #[x₂, y] == mkApp (mkBVar 1) (mkBVar 0)}"
  IO.println s!"whole-array: {term.abstract #[x₂, y] == mkApp (mkBVar 1) (mkBVar 0)}"
  IO.println s!"reverse-duplicate: {x.abstractRange 3 #[x₂, y, x₂] == mkBVar 0}"
  IO.println s!"domain-distinct: {mx.abstractRange 1 #[x₂] == mx}"
  IO.println s!"mvar-match: {mx.abstractRange 1 #[mx] == mkBVar 0}"
  let lam := mkLambda `z BinderInfo.default (mkSort .zero) (mkApp x (mkBVar 0))
  let expected := mkLambda `z BinderInfo.default (mkSort .zero) (mkApp (mkBVar 1) (mkBVar 0))
  IO.println s!"binder-offset: {lam.abstractRange 1 #[x₂] == expected}"
  IO.println s!"ignored-nonvar: {x.abstractRange 2 #[mkSort .zero, x₂] == mkBVar 0}"
  IO.println s!"huge-nat: {x.abstractRange (2^100) #[x₂, y] == mkBVar 1}"
