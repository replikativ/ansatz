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

-- Shared binders must use the same inference cache across local extensions.
run_meta do
  let mut term := mkSort Level.zero
  for _ in [:40] do
    term := mkForall `x BinderInfo.default term term
  unless (← inferType term) == mkSort (Level.succ Level.zero) do
    throwError "incorrect shared arrow universe"

-- A local's type is returned directly, regardless of its syntax depth.
set_option maxRecDepth 10000 in
run_meta do
  let nat := mkConst ``Nat
  withLocalDeclD `x nat fun x => do
    withLocalDeclD `P (← mkArrow nat (mkSort Level.zero)) fun p => do
      let mut term := x
      for _ in [:2000] do
        term := mkApp (mkConst ``Nat.succ) term
      let ty := mkApp p term
      withLocalDeclD `h ty fun h => do
        unless (← inferType h) == ty do
          throwError "incorrect deep local type"

-- Metadata is transparent, including in a deep cached open expression.
set_option maxRecDepth 10000 in
run_meta do
  let nat := mkConst ``Nat
  withLocalDeclD `x nat fun x => do
    withLocalDeclD `P (← mkArrow nat (mkSort Level.zero)) fun p => do
      let mut term := x
      for _ in [:3000] do
        term := mkApp (mkConst ``Nat.succ) term
      let ty := mkApp p term
      withLocalDeclD `h ty fun h => do
        let mut expr := h
        for _ in [:3000] do
          expr := mkMData {} expr
        unless (← inferType expr) == ty do
          throwError "incorrect deep metadata type"
