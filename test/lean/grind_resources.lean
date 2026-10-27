import Lean

open Lean Meta

-- Cached transform visits each shared node once before simplification.
run_meta do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    for depth in #[16, 40] do
      let mut term := x
      for _ in [:depth] do
        term := mkApp2 (mkConst ``Nat.add) term term
      let visits ← IO.mkRef 0
      let result ← Core.transform (m := MetaM) term (post := fun e => do
        visits.modify (· + 1)
        return .done e)
      unless (← visits.get) ≤ 2 * depth + 2 do
        throwError "transform expanded the shared DAG"
      unless result.getAppArgs[0]! == result.getAppArgs[1]! do
        throwError "transform lost shared arguments"

-- simpLoop numSteps is carried in Simp.State; cache hits do not charge work.
run_meta do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let term := mkApp2 (mkConst ``Nat.add) x (mkNatLit 0)
    let ctx ← Simp.mkContext (config := { maxSteps := 100, arith := false })
    let (_, state) ← simpCore term ctx
    let (_, again) ← simpCore term ctx (s := state)
    unless state.numSteps > 0 && again.numSteps == state.numSteps do
      throwError "incorrect simp work accounting"

-- withApp iterates flat argument spines (also used by internalizeImpl).
run_meta do
  let nat := mkConst ``Nat
  let mut fnType := nat
  for _ in [:1000] do
    fnType := mkForall `a BinderInfo.default nat fnType
  withLocalDeclD `f fnType fun f =>
    withLocalDeclD `x nat fun x => do
      let mut term := f
      for _ in [:1000] do
        term := mkApp term x
      let visits ← IO.mkRef 0
      discard <| Core.transform (m := MetaM) term (post := fun e => do
        visits.modify (· + 1)
        return .done e)
      unless (← visits.get) == 3 do
        throwError "flat arity was treated as recursion depth"

example (f : Nat → Nat) (a b x y : Nat) (h : a = b) :
    (f a + x) + y = f b + (x + y) := by
  grind
