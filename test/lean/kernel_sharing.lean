import Lean

open Lean Meta

-- The term has linear DAG size and exponential tree size.
run_meta do
  let prop := mkSort Level.zero
  let fnType ← mkArrow prop (← mkArrow prop prop)
  withLocalDeclD `f fnType fun f =>
    withLocalDeclD `x prop fun x => do
      let mut term := x
      for _ in [:40] do
        term := mkApp2 f term term
      let closed := term.abstract #[x]
      unless closed.instantiate1 x == term do
        throwError "abstraction/instantiation changed the shared term"
      unless (← inferType term) == prop do
        throwError "incorrect shared term type"
      let proofType := mkForall `h BinderInfo.default closed (closed.liftLooseBVars 0 1)
      let lam := mkLambda `x BinderInfo.default prop
        (mkLambda `h BinderInfo.default closed (mkBVar 0))
      unless (← inferType lam) == mkForall `x BinderInfo.default prop proofType do
        throwError "incorrect dependent lambda type"
