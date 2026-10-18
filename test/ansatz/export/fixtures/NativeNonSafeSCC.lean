import Lean

/-!
Tiny native KERNEL admission oracle, not a surface partial-compilation fixture.
Both blocks are checked by the pinned native kernel before being serialized.
The unsafe/partial inhabitants of P must never become safe theorem evidence.
-/
open Lean Elab Command in
run_elab do
  let p := `NativeNonSafeSCC.P
  let mut env := ← getEnv
  let assumption : Declaration := .axiomDecl {
    name := p, levelParams := [], type := mkSort .zero, isUnsafe := false
  }
  match env.addDeclCore 1000000 1000 assumption none with
  | .ok next => env := next
  | .error _ => throwError "Native SCC axiom admission failed"
  for (safety, left, right) in [
      (DefinitionSafety.unsafe, `NativeNonSafeSCC.unsafeLeft, `NativeNonSafeSCC.unsafeRight),
      (DefinitionSafety.partial, `NativeNonSafeSCC.partialLeft, `NativeNonSafeSCC.partialRight)] do
    let first : DefinitionVal := {
      name := left, levelParams := [], type := mkConst p, value := mkConst right,
      hints := .opaque, safety := safety, all := [left, right]
    }
    let second : DefinitionVal := { first with name := right, value := mkConst left }
    match env.addDeclCore 1000000 1000 (.mutualDefnDecl [first, second]) none with
    | .ok next => env := next
    | .error _ => throwError "Native SCC mutual admission failed"
    let invalidProof : Declaration := .thmDecl {
      name := .str left "invalidSafeProof", levelParams := [],
      type := mkConst p, value := mkConst left
    }
    match env.addDeclCore 1000000 1000 invalidProof none with
    | .error _ => pure ()
    | .ok _ => throwError "Native kernel accepted non-safe constant as safe proof"
  setEnv env
