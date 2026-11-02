import Lean
open Lean

@[extern "ansatz111_reset_kernel_hb"] opaque resetKernelHB : IO Unit

-- Build raw kernel expressions, avoiding elaborator normalization of 24 + 0.
def projectionModel (n : Nat) : Declaration := Id.run do
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
  let iter := fun k => mkApp4 (mkConst ``Nat.rec [Level.succ u])
    (mkLambda `_ .default nat pairType) base step k
  let lhs := mkApp (first (iter (mkNatLit n))) (mkBVar 0)
  let rhs := mkApp (first (iter (mkApp2 (mkConst ``Nat.add) (mkNatLit n) (mkNatLit 0))))
    (mkBVar 0)
  let goal := mkApp3 (mkConst ``Eq [Level.succ u]) nat lhs rhs
  let proof := mkApp2 (mkConst ``Eq.refl [Level.succ u]) nat lhs
  return .thmDecl {
    name := `Issue111.projectionModel
    levelParams := []
    type := mkForall `x .default nat goal
    value := mkLambda `x .default nat proof
    all := [`Issue111.projectionModel]
  }

unsafe def main (args : List String) : IO UInt32 := do
  let some root ← IO.getEnv "LEAN_SYSROOT" | throw <| IO.userError "set LEAN_SYSROOT"
  initSearchPath root
  let n := args.head?.bind String.toNat? |>.getD 24
  withImportModules #[{module := `Init}] {} fun env => do
    IO.setNumHeartbeats 0
    resetKernelHB
    let start ← IO.monoMsNow
    -- Force the kernel result before collecting the end time/allocation count.
    match env.toKernelEnv.addDeclCore 100000 0 (projectionModel n) none with
    | .ok _ =>
      IO.println s!"checked n={n} elapsed_ms={(← IO.monoMsNow) - start} allocations={(← IO.getNumHeartbeats)}"
      return 0
    | .error ex =>
      IO.println s!"failed n={n} elapsed_ms={(← IO.monoMsNow) - start} allocations={(← IO.getNumHeartbeats)}"
      IO.println <| ← ex.toMessageData {} |>.toString
      return if let .deterministicTimeout := ex then 2 else 1
