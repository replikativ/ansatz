import SourceModuleGraphImport
import SourceModuleExport

open Lean SourceModuleImport SourceModuleGraphImport

private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", encodeName p, toJson s]
  | .num p n => Json.arr #[toJson "num", encodeName p, toJson (toString n)]

private def compile (env : Environment) (name : Name) (text : String) : IO Environment := do
  let input := Parser.mkInputContext text (name.toString ++ ".lean")
  let (header, pos, messages) ← Parser.parseHeader input
  unless !messages.hasErrors && Elab.HeaderSyntax.imports header == env.header.imports do
    throw <| IO.userError "graph oracle header mismatch"
  let state ← Elab.IO.processCommands input pos
    (Elab.Command.mkState (env.setMainModule name) messages {})
  if state.commandState.messages.hasErrors then
    for msg in state.commandState.messages.toList do IO.eprintln (← msg.toString)
    throw <| IO.userError "graph oracle compilation failed"
  return state.commandState.env

private def limits : GraphLimits := {
  maxModules := 1024, maxRoots := 16, maxEdges := 64, maxDepth := 16,
  maxNames := 1000000, maxNameNodes := 128, maxNameBytes := 4096,
  maxTotalNameBytes := 67108864, maxKeyBytes := 4096, maxTotalKeyBytes := 16384}

private def requests (root : Name) : Array Import :=
  #[{module := `Init}, {module := `Init, isMeta := true}, {module := root}]

private def check (p : Bool) (message : String) : IO Unit :=
  unless p do throw <| IO.userError message

private def stage (label : String) : IO Unit := do
  let err ← IO.getStderr
  err.putStrLn ("graph-oracle: " ++ label)
  err.flush

private def importJson (i : EffectiveImport) : Json := Json.mkObj [
  ("module", encodeName i.module), ("importAll", toJson i.importAll),
  ("isExported", toJson i.isExported), ("isMeta", toJson i.isMeta),
  ("hasData", toJson i.hasData), ("irPhases", toJson (reprStr i.irPhases))]

unsafe def main (args : List String) : IO Unit := do
  let [fixtureDir, outputDir] := args | throw <| IO.userError "expected fixture/output directories"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  IO.FS.createDirAll outputDir
  searchPathRef.modify (fun paths => System.FilePath.mk outputDir :: paths)
  let init : Array Import := #[{module := `Init}, {module := `Init, isMeta := true}]
  stage "native-prefix-start"
  let (_, nativePrefixState) ← (importModulesCore (globalLevel := .private) init).run
  stage "native-prefix-ready"
  let prefixView : ImportStateView := unsafeCast nativePrefixState
  -- Finalize the actual native prefix once instead of reading Init a second
  -- time. Both source chains already share this immutable native starting base.
  let base ← finalizeClassic nativePrefixState init {}
  stage "native-base-ready"
  let names := #[`GraphOracleA, `GraphOracleB, `GraphOracleC]
  let mut ownedBase := base
  let mut parts : Array GraphPartInput := #[]
  let mut sourceJson := #[]
  for name in names do
    stage ("owned-compile-" ++ name.toString)
    let text ← IO.FS.readFile (System.FilePath.mk fixtureDir / (name.toString ++ ".lean"))
    let compiled ← compile ownedBase name text
    let (data, metadata) ← SourceModuleExport.exportClassic compiled name
    sourceJson := sourceJson.push (← IO.ofExcept (Json.parse metadata))
    parts := parts.push {moduleName := name, data, key := "ansatz-source:graph-oracle:" ++ name.toString}
    stage ("owned-assemble-" ++ name.toString)
    let assembled ← IO.ofExcept (assembleClassicGraphOverInit nativePrefixState parts (requests name) limits)
    -- Direct finalization only, leakEnv=false in unchanged finalizeClassic.
    -- No logical-region free, withImportModules cleanup, snapshot serialization,
    -- or native region read/save is allowed anywhere in this owned chain.
    stage ("owned-finalize-" ++ name.toString)
    ownedBase ← finalizeClassic assembled.state assembled.imports {}
    stage ("owned-ready-" ++ name.toString)
  -- The driver independently compiles the exact A/B/C texts with the pinned
  -- Lean CLI into outputDir before running this oracle. Import that reference
  -- chain once; never overwrite it or serialize logical owned source data.
  stage "disk-import-GraphOracleC"
  -- withImporting clears this flag after every finalization.
  enableInitializersExecution
  let diskBase ← importModules (requests `GraphOracleC) {} (loadExts := true)
  stage "disk-ready-GraphOracleC"
  stage "compare"
  check (ownedBase.header.imports == requests `GraphOracleC &&
    diskBase.header.imports == requests `GraphOracleC) "final graph consumer header mismatch"
  check (ownedBase.header.modules.size == diskBase.header.modules.size) "graph module count differs"
  for h : i in [:ownedBase.header.modules.size] do
    check (importJson ownedBase.header.modules[i] == importJson diskBase.header.modules[i]!)
      "graph module order/effective flags differ"
  check (ownedBase.const2ModIdx.size == diskBase.const2ModIdx.size) "graph attribution count differs"
  for (name, index) in ownedBase.const2ModIdx do
    check (diskBase.getModuleIdxFor? name == some index) "graph CI/extra attribution differs"
  for env in #[ownedBase, diskBase] do
    let nat ← IO.ofExcept <| env.evalConst (Nat → Nat) {} `GraphOracleC.nat
    let text ← IO.ofExcept <| env.evalConst (String → String) {} `GraphOracleC.text
    check (nat 41 == 43 && text "Ω" == "Ωλλ") "graph Nat/String result differs"
  let some partA := parts[0]? | throw <| IO.userError "missing oracle A"
  let some partB := parts[1]? | throw <| IO.userError "missing oracle B"
  let some partC := parts[2]? | throw <| IO.userError "missing oracle C"
  stage "negative-cases"
  -- Pure helper negative tests reuse actual data; no rejected path finalizes.
  let expectRejected := fun (p : Array GraphPartInput) (r : Array Import) => do
    match assembleClassicGraphOverInit nativePrefixState p r limits with
    | .error _ => pure ()
    | .ok _ => throw <| IO.userError "unsupported graph accepted"
  expectRejected parts (requests `GraphOracleA)
  expectRejected #[partB, partA, partC] (requests `GraphOracleC)
  expectRejected parts ((requests `GraphOracleC).set! 2 {module := `GraphOracleC, isMeta := true})
  let mut collision := partC
  collision := {collision with data := {collision.data with extraConstNames := #[`GraphOracleA.nat]}}
  expectRejected (parts.set! 2 collision) (requests `GraphOracleC)
  let cyclicA := {partA with data := {partA.data with imports := requests `GraphOracleC}}
  expectRejected (parts.set! 0 cyclicA) (requests `GraphOracleC)
  let missingB := {partB with data := {partB.data with imports := requests `GraphOracleMissing}}
  expectRejected (parts.set! 1 missingB) (requests `GraphOracleC)
  let nativeCollision := {partC with data := {partC.data with extraConstNames := #[`Nat.add]}}
  expectRejected (parts.set! 2 nativeCollision) (requests `GraphOracleC)
  match assembleClassicGraphOverInit nativePrefixState parts (requests `GraphOracleC) {limits with maxDepth := 2} with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "over-depth graph accepted"
  -- Explicit graph-profile Name/key boundaries; never finalize synthetic data.
  let maxNatC := {partC with data := {partC.data with extraConstNames := #[.num .anonymous 4294967295]}}
  let _ ← IO.ofExcept <| assembleClassicGraphOverInit nativePrefixState
    (parts.set! 2 maxNatC) (requests `GraphOracleC) limits
  let overNatC := {partC with data := {partC.data with extraConstNames := #[.num .anonymous 4294967296]}}
  expectRejected (parts.set! 2 overNatC) (requests `GraphOracleC)
  let oversized := String.ofList (List.replicate 4097 'x')
  let overNameC := {partC with data := {partC.data with extraConstNames := #[.str .anonymous oversized]}}
  expectRejected (parts.set! 2 overNameC) (requests `GraphOracleC)
  expectRejected (parts.set! 2 {partC with key := oversized}) (requests `GraphOracleC)
  -- Structural diamond only: no finalization/evaluation of these synthetic data.
  let diamondC := {partC with data := {partC.data with imports := requests `GraphOracleA}}
  let diamondD : GraphPartInput := {
    moduleName := `GraphOracleD, key := "ansatz-source:graph-oracle:D",
    data := {
      isModule := false, imports := (requests `GraphOracleB).push {module := `GraphOracleC},
      constNames := #[], constants := #[], extraConstNames := #[], entries := #[]}}
  let diamond ← IO.ofExcept <| assembleClassicGraphOverInit nativePrefixState
    #[partA, partB, diamondC, diamondD] (requests `GraphOracleD) limits
  let diamondView : ImportStateView := unsafeCast diamond.state
  check (diamondView.moduleNames == prefixView.moduleNames ++
    #[`GraphOracleA, `GraphOracleB, `GraphOracleC, `GraphOracleD]) "diamond DFS order mismatch"
  stage "passed"
  IO.println (Json.mkObj [
    ("schema", toJson "ansatz-source-graph-native-oracle/1"),
    ("leanCommit", toJson Lean.githash),
    ("nativePrefix", toJson (prefixView.moduleNames.map encodeName)),
    ("sourceModules", Json.arr sourceJson),
    ("modules", toJson (ownedBase.header.modules.map importJson)),
    ("attributionEntriesCompared", toJson ownedBase.const2ModIdx.size),
    ("sourceCount", toJson parts.size), ("structuralDiamond", toJson true), ("negativeCases", toJson (11 : Nat)), ("acceptedNumericBoundary", toJson true),
    ("nat", toJson (43 : Nat)), ("text", toJson "Ωλλ"),
    ("logicalRegionsSerialized", toJson false), ("logicalRegionsFreed", toJson false)]).compress
