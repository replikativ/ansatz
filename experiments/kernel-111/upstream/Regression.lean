import Lean
open Lean

-- Build raw kernel expressions so elaboration cannot normalize away 24 + 0.
-- The Fin binder comparison precedes the computed-projection comparison.
-- The beta redex makes the old post-whnf recursive cache lookup applicable.
def projectionModel (n : Nat) : Declaration × Declaration := Id.run do
  let nat := mkConst ``Nat
  let u := Level.zero
  let fnType := mkForall `x .default nat nat
  let pairType := mkApp2 (mkConst ``Prod [u, u]) fnType nat
  let pair := fun f => mkApp4 (mkConst ``Prod.mk [u, u]) fnType nat f (mkNatLit 0)
  let first := fun p => mkProj ``Prod 0 p
  let base := pair (mkLambda `x .default nat (mkBVar 0))
  let previous := first (mkBVar 1)
  let step := mkLambda `k .default nat <| mkLambda `prev .default pairType <|
    pair (mkLambda `x .default nat (mkApp previous (mkApp previous (mkBVar 0))))
  let iterBody := fun k => mkApp4 (mkConst ``Nat.rec [Level.succ u])
    (mkLambda `_ .default nat pairType) base step k
  let iterator := Declaration.defnDecl {
    name := `ProjectionRegression.iterator
    levelParams := []
    type := mkForall `n .default nat pairType
    value := mkLambda `n .default nat (iterBody (mkBVar 0))
    hints := .regular 1
    safety := .safe
    all := [`ProjectionRegression.iterator]
  }
  let iter := fun k => mkApp (mkConst `ProjectionRegression.iterator) k
  let lhs := mkApp (first (iter (mkNatLit n))) (mkBVar 0)
  let rhs := mkApp (first (iter (mkApp2 (mkConst ``Nat.add) (mkNatLit n) (mkNatLit 0))))
    (mkBVar 0)
  let count := mkNatLit n
  let countPlusZero := mkApp2 (mkConst ``Nat.add) count (mkNatLit 0)
  let goal := mkApp3 (mkConst ``Eq [Level.succ u]) nat lhs rhs
  let betaLhs := mkApp (mkLambda `unused .default nat (lhs.liftLooseBVars 0 1)) (mkNatLit 0)
  let proof := mkApp2 (mkConst ``Eq.refl [Level.succ u]) nat betaLhs
  return (iterator, .thmDecl {
    name := `ProjectionRegression.projectionModel
    levelParams := []
    type := mkForall `a .default (mkApp (mkConst ``Fin) countPlusZero)
      (mkForall `x .default nat goal)
    value := mkLambda `a .default (mkApp (mkConst ``Fin) count)
      (mkLambda `x .default nat proof)
    all := [`ProjectionRegression.projectionModel]
  })

unsafe def main (args : List String) : IO UInt32 := do
  let some root ← IO.getEnv "LEAN_SYSROOT" | throw <| IO.userError "set LEAN_SYSROOT"
  initSearchPath root
  let n := args.head?.bind String.toNat? |>.getD 24
  withImportModules #[{module := `Init}] {} fun env => do
    let (iterator, thm) := projectionModel n
    let .ok kernelEnv := env.toKernelEnv.addDeclCore 0 0 iterator none
      | throw <| IO.userError "failed iterator declaration"
    -- Allocation heartbeats only. The kernel budget below is cumulative within
    -- this fresh native process, including the small iterator check above.
    IO.setNumHeartbeats 0
    let start ← IO.monoMsNow
    -- Force the kernel result before collecting the end time/allocation count.
    match kernelEnv.addDeclCore 100000 0 thm none with
    | .ok _ =>
      IO.println s!"checked n={n} elapsed_ms={(← IO.monoMsNow) - start} allocations={(← IO.getNumHeartbeats)}"
      return 0
    | .error ex =>
      IO.println s!"failed n={n} elapsed_ms={(← IO.monoMsNow) - start} allocations={(← IO.getNumHeartbeats)}"
      IO.println <| ← ex.toMessageData {} |>.toString
      return if let .deterministicTimeout := ex then 2 else 1
