import RuntimeCompileShim

open Lean Lean.IR

private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", encodeName p, toJson s]
  | .num p n => Json.arr #[toJson "num", encodeName p, toJson (toString n)]

private def rowJson (row : RuntimeCompileShim.EvalConstWitnessIRRow) : Json :=
  Json.mkObj [("name", encodeName row.name), ("ir", toJson row.decl),
    ("sourceLocal", toJson row.sourceLocal), ("sourceModule", (row.sourceModule.map encodeName).getD Json.null)]

private def witnessJson (w : RuntimeCompileShim.EvalConstWitnessIR) : Json :=
  Json.mkObj [("schema", toJson w.schema), ("producer", toJson w.producer),
    ("leanCommit", toJson w.leanCommit),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson w.wordBits), ("target", toJson w.target)]),
    ("name", encodeName w.name), ("boxedTarget", encodeName w.boxedTarget),
    ("declarations", Json.arr (w.rows.map rowJson)),
    ("missingDependencies", Json.arr (w.missingDependencies.map encodeName)),
    ("sorryDep", (w.sorryDep.map encodeName).getD Json.null)]

private unsafe def actualInitOracle : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Init}, {module := `Init, isMeta := true}] {} 0 (loadExts := true) (level := .private)
  let name := Name.str .anonymous "_aux_Init_Data_UInt_Lemmas___macroRules_commandDeclare_uint_theorems___1"
  let started ← IO.monoMsNow
  let original ← RuntimeCompileShim.exportEvalConstWitness env name
  let originalMs := (← IO.monoMsNow) - started
  let started ← IO.monoMsNow
  let shared ← RuntimeCompileShim.exportEvalConstWitnessIRSharedNames env name
  let sharedMs := (← IO.monoMsNow) - started
  let started ← IO.monoMsNow
  let candidate ← RuntimeCompileShim.exportEvalConstWitnessIRSharedNamesLinear env name
  let linearMs := (← IO.monoMsNow) - started
  unless candidate.rows.any (fun row => row.name == name && match row.decl with
      | .fdecl .. => true
      | _ => false) do
    throw <| IO.userError "Actual failed UInt macro body was not selected; missing/extern witness is not a parity result"
  unless candidate.missingDependencies.isEmpty && candidate.sorryDep.isNone do
    throw <| IO.userError "Actual UInt witness has missing dependencies or sorry evidence"
  unless (witnessJson shared).compress == original && (witnessJson candidate).compress == original do
    throw <| IO.userError "Actual failed UInt macro witness parity failed"
  -- Only new output paths; stdout stays bounded. Shell computes SHA256 of the
  -- exact compared payloads, rather than calling a noncryptographic hash digest.
  IO.FS.writeFile "target/witness-ir-shared-names-linear/init-original.json" original
  IO.FS.writeFile "target/witness-ir-shared-names-linear/init-shared-linear.json" (witnessJson candidate).compress
  IO.println <| (Json.mkObj [("scope", toJson "native-actual-Init-failed-UInt-macro"),
    ("exactParity", toJson true), ("declarations", toJson candidate.rows.size),
    ("missing", toJson candidate.missingDependencies.size), ("bytes", toJson original.utf8ByteSize),
    ("originalStringMs", toJson originalMs), ("sharedMs", toJson sharedMs),
    ("sharedLinearMs", toJson linearMs)]).compress

#eval actualInitOracle
