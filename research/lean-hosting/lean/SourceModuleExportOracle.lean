import SourceModuleExport

open Lean

private def compile (env : Environment) (name : Name) (text : String) : IO Environment := do
  let input := Parser.mkInputContext text (name.toString ++ ".lean")
  let (header, pos, messages) ← Parser.parseHeader input
  if messages.hasErrors then
    for msg in messages.toList do IO.eprintln (← msg.toString)
  unless !messages.hasErrors && Elab.HeaderSyntax.imports header == env.header.imports do
    throw <| IO.userError s!"oracle header mismatch for {name}: actual {repr (Elab.HeaderSyntax.imports header)}, expected {repr env.header.imports}"
  let state ← Elab.IO.processCommands input pos
    (Elab.Command.mkState (env.setMainModule name) messages {})
  if state.commandState.messages.hasErrors then
    for msg in state.commandState.messages.toList do
      IO.eprintln (← msg.toString)
    throw <| IO.userError "oracle compilation failed"
  return state.commandState.env

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports : Array Import := #[{module := `Init}, {module := `Init, isMeta := true}]
  let base ← importModules imports {} (loadExts := true)
  let a ← compile base `SourceOracleA "def sourceAnswer : Nat := 42\n"
  let (data, metadata) ← SourceModuleExport.exportClassic a `SourceOracleA
  unless data.constNames.contains `sourceAnswer && !data.isModule && data.imports == imports do
    throw <| IO.userError "source ModuleData lost constants/imports"
  unless data.entries.any (fun (name, _) => name == IR.declMapExt.name) do
    throw <| IO.userError "source ModuleData lost compiler IR extension"
  -- Native disk import is the oracle, not the hosted implementation. The source
  -- helper itself returns the owned ModuleData before any native serialization.
  IO.FS.createDirAll "target/source-module-oracle"
  writeModule a "target/source-module-oracle/SourceOracleA.olean"
  searchPathRef.modify (fun paths => "target/source-module-oracle" :: paths)
  let bImports : Array Import := imports ++ #[{module := `SourceOracleA}]
  enableInitializersExecution
  let bBase ← importModules bImports {} (loadExts := true)
  let b ← compile bBase `SourceOracleB "import SourceOracleA\ndef sourceNext : Nat := sourceAnswer + 1\n"
  let value ← IO.ofExcept <| b.evalConst Nat {} `sourceNext
  unless value == 43 do throw <| IO.userError s!"A→B oracle returned {value}"
  IO.println metadata
  IO.println (Json.mkObj [("case", toJson "native-A-to-B"), ("result", toJson value)]).compress
  let moduleEnv ← importModules #[] {} (level := .exported)
  for (env, expected) in #[(a, `WrongModule), (a, Name.anonymous),
      (moduleEnv.setMainModule `SourceOracleA, `SourceOracleA)] do
    let rejected ← try
      let _ ← SourceModuleExport.exportClassic env expected
      pure false
    catch _ => pure true
    unless rejected do throw <| IO.userError "unsupported export was accepted"

