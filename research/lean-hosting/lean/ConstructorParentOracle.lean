import Lean

-- Raw kernel declarations bypass elaborator diagnostics. Both safety modes must
-- reject a constructor returning another member of the same mutual declaration.
#eval show Lean.CoreM Unit from do
  let base := (← Lean.getEnv).toKernelEnv
  for unsafeFlag in [false, true] do
    for wrong in [false, true] do
      let a := `ConstructorParentOracle.A
      let b := `ConstructorParentOracle.B
      let decl : Lean.Declaration := .inductDecl [] 0 [
        { name := a, type := Lean.mkSort 1,
          ctors := [{ name := a ++ `mk, type := Lean.mkConst (if wrong then b else a) }] },
        { name := b, type := Lean.mkSort 1,
          ctors := [{ name := b ++ `mk, type := Lean.mkConst b }] }
      ] unsafeFlag
      match base.addDeclCore 0 1000 decl none with
      | .ok _ =>
        if wrong then throwError "kernel unexpectedly accepted wrong constructor parent"
        else IO.println s!"accepted correct parent, unsafe={unsafeFlag}"
      | .error _ =>
        if wrong then IO.println s!"rejected wrong parent, unsafe={unsafeFlag}"
        else throwError "kernel rejected correct parent"
