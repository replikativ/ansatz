import SourceModuleImport
import SourceModuleExport

open Lean

private def compile (env : Environment) (name : Name) (text : String) : IO Environment := do
  let input := Parser.mkInputContext text (name.toString ++ ".lean")
  let (header, pos, messages) ← Parser.parseHeader input
  unless !messages.hasErrors && Elab.HeaderSyntax.imports header == env.header.imports do
    throw <| IO.userError "source oracle header mismatch"
  let state ← Elab.IO.processCommands input pos
    (Elab.Command.mkState (env.setMainModule name) messages {})
  if state.commandState.messages.hasErrors then
    for msg in state.commandState.messages.toList do IO.eprintln (← msg.toString)
    throw <| IO.userError "source oracle compilation failed"
  return state.commandState.env

unsafe def main : IO Unit := do
  let mut env ← mkEmptyEnvironment
  for name in [`lcAny, `lcErased, `lcVoid] do
    env ← IO.ofExcept <| env.addDeclCore 1000000 1000
      (.axiomDecl {name, levelParams := [], type := mkSort (.succ .zero), isUnsafe := true}) none
      |>.mapError (fun _ => "marker admission failed")
  let a ← compile env `PreludeIdentity "prelude\ndef answer.{u} (α : Sort u) (x : α) : α := x\n"
  let (data, _) ← SourceModuleExport.exportClassic a `PreludeIdentity
  unless data.constants.size == 4 && data.imports.isEmpty do
    throw <| IO.userError "source oracle expected four constants and no imports"
  let assembly := SourceModuleImport.assembleClassic data `PreludeIdentity "ansatz-source:native-oracle"
  -- This path does not serialize or mmap anything and must never call native
  -- CompactedRegion.free on its logical region. Ordinary Lean refs own the data.
  let imported ← SourceModuleImport.finalizeClassic assembly.state assembly.imports {}
  unless imported.header.imports == #[{module := `PreludeIdentity}] &&
      imported.toKernelEnv.quotInit && (imported.getModuleIdxFor? `answer).map ModuleIdx.toNat == some 0 do
    throw <| IO.userError "real source finalizer header/provenance mismatch"
  let b ← compile imported `PreludeSecond
    "prelude\nimport PreludeIdentity\ndef second.{u} (α : Sort u) (x : α) : α := answer α x\n"
  let second ← IO.ofExcept <| b.evalConst (Unit → Nat → Nat) {} `second (checkMeta := false)
  unless second () 42 == 42 do throw <| IO.userError "source A→B result mismatch"
  IO.println (SourceModuleImport.finalizerHeader imported)
  IO.println "source-owned-module-A-to-B: 42"
