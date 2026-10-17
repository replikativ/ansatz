import RuntimeCompileShim

open Lean

namespace RuntimeCompileShimInitializerTests
unsafe def run : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Init}, {module := `Init, isMeta := true}] {} 0 (loadExts := true)
  let source := "initialize\n  IO.println \"SOURCE_REGULAR_INIT_RAN\"\nbuiltin_initialize\n  IO.println \"SOURCE_BUILTIN_INIT_RAN\"\nmacro \"localFortyTwo\" : term => `(42)\ndef answer : Nat := localFortyTwo\n"
  let (env, result) ← RuntimeCompileShim.compileImportedFileState env source
    "InitEffects.lean" `InitEffects #[`answer] {}
  let j ← IO.ofExcept (Json.parse result)
  unless (← IO.ofExcept (j.getObjValAs? Bool "success")) do
    throw <| IO.userError result
  unless (← IO.ofExcept (env.evalConst Nat {} `answer)) == 42 do
    throw <| IO.userError "local macro did not execute"
  let a ← RuntimeCompileShim.exportCompiled env #[`answer]
  let b ← RuntimeCompileShim.exportCompiled env #[`answer]
  unless a == b do throw <| IO.userError "repeated export differs"
  let first := a.splitOn "\n" |>.head!
  let manifest ← IO.ofExcept (Json.parse first)
  let plan ← IO.ofExcept (manifest.getObjVal? "initializationPlan")
  let actions ← IO.ofExcept (plan.getObjValAs? (Array Json) "actions")
  unless actions.size >= 3 do throw <| IO.userError "source initializers/macro registration absent from plan"
  IO.println s!"PASS local macro=42, repeated export, future initializer actions={actions.size}"
  IO.println "NO SOURCE INITIALIZER EFFECT SHOULD APPEAR ABOVE"
end RuntimeCompileShimInitializerTests

#eval RuntimeCompileShimInitializerTests.run
