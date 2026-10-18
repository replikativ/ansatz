import RuntimeCompileShim

open Lean Lean.IR

namespace UIntCollectorBodyCanary

/-- Oracle-only generic object-array ABI. The primary export is genuinely
Array FnBody. Additional explicitly labeled Decl/Json payloads use unsafeCast
ONLY to pass their identical Array object ABI to the same native DAG walker. -/
@[extern "module_data_transport_export"]
unsafe opaque exportDAG
  (roots : @& Array IR.FnBody) (metadata : @& String) (path : @& String)
  (verify : Bool) : IO String

private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", encodeName p, toJson s]
  | .num p n => Json.arr #[toJson "num", encodeName p, toJson (toString n)]

private def culprit : Name :=
  .str .anonymous "_aux_Init_Data_UInt_Lemmas___macroRules_commandDeclare_uint_theorems___1"

private def metadata (kind : String) (source : Name) (count : Nat) : Json :=
  Json.mkObj [
    ("schema", toJson "lean-module-data-input/1"),
    ("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
    -- Legacy transport-profile flag describes the PAYLOAD (no finalized Env),
    -- while the separate explicit selector flag records the genuine native import.
    ("nativeEnvironmentFinalized", toJson false),
    ("nativeSelectionEnvironmentFinalized", toJson true),
    ("nativeEnvironmentTransported", toJson false),
    ("regionAddressesTransported", toJson false),
    ("globalLevel", toJson "private"), ("requestedImports", Json.arr #[]),
    ("transitiveClosure", toJson false), ("modules", Json.arr #[]),
    ("canary", toJson true), ("oracle", toJson "actual-interpreter-selected-FnBody/1"),
    ("rootValueKind", toJson kind), ("selectedName", encodeName culprit),
    ("sourceModule", encodeName source), ("sourceLocal", toJson false),
    ("selection", toJson "RuntimeCompileShim.exportEvalConstWitnessIRSharedNamesLinear"),
    ("selectionImports", Json.arr #[
      Json.mkObj [("module", encodeName `Init), ("importAll", toJson false),
        ("isExported", toJson true), ("isMeta", toJson false)],
      Json.mkObj [("module", encodeName `Init), ("importAll", toJson false),
        ("isExported", toJson true), ("isMeta", toJson true)]]),
    ("selectionLevel", toJson "private"), ("selectionModuleSystem", toJson false),
    ("missingDependencies", Json.arr #[]), ("sorryDep", Json.null),
    ("dependencyCount", toJson count)]

private unsafe def compactAndExport {α : Type} (values : Array α)
    (moduleName : Name) (metadata : Json) (path : String) : IO Unit := do
  let nativeFile : System.FilePath := path ++ ".native-v2"
  let _ ← CompactedRegion.save nativeFile moduleName values #[] none
  let (compacted, region) ← CompactedRegion.read (α := Array α) nativeFile #[]
  let result ← exportDAG (unsafeCast compacted) metadata.compress path true
  -- FilePath use after export keeps the native region record visibly live.
  -- No native CompactedRegion.free/unmap is called by this oracle.
  unless region.filePath == nativeFile do
    throw <| IO.userError "Compacted canary source path drift"
  IO.println result

unsafe def run (outputPrefix : String) : IO Unit := do
  unless Lean.githash == "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" do
    throw <| IO.userError "Actual body oracle requires pinned Lean4.33.1"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `Init}, {module := `Init, isMeta := true}] {} 0
    (loadExts := true) (level := .private)
  unless env.header.imports == #[{module := `Init}, {module := `Init, isMeta := true}]
      && !env.header.isModule do
    throw <| IO.userError "Actual Init import/header policy drift"
  let witness ← RuntimeCompileShim.exportEvalConstWitnessIRSharedNamesLinear env culprit
  unless witness.name == culprit && witness.leanCommit == Lean.githash &&
      witness.wordBits == 64 && witness.target == "x86_64-unknown-linux-gnu" &&
      witness.schema == "lean-eval-const-witness/1" &&
      witness.producer == "RuntimeCompileShim.exportEvalConstWitness" &&
      witness.missingDependencies.isEmpty && witness.sorryDep.isNone do
    throw <| IO.userError "Interpreter-selected UInt witness profile/missing/sorry failure"
  let matching := witness.rows.filter (·.name == culprit)
  unless matching.size == 1 do
    throw <| IO.userError "Expected exactly one interpreter-selected original root"
  let some selected := matching[0]?
    | throw <| IO.userError "Interpreter-selected root disappeared"
  unless !selected.sourceLocal && selected.sourceModule == some `Init.Data.UInt.Lemmas do
    throw <| IO.userError "Actual UInt root must be imported from Init.Data.UInt.Lemmas"
  let .fdecl actualName _ _ body _ := selected.decl
    | throw <| IO.userError "Missing/extern root is not an actual FnBody canary"
  unless actualName == culprit do
    throw <| IO.userError "Selected declaration name differs from actual culprit"
  -- Both actual native collectors see the same selected body, with exact order
  -- and duplicate retention. This is a native semantic oracle, not guest fuel.
  let original := RuntimeCompileShim.bodyDepsOriginalOnlyProbe body
  let linear := RuntimeCompileShim.bodyDepsLinearOnlyProbe body
  unless original == linear do
    throw <| IO.userError "Actual body native collector order/multiplicity mismatch"
  let source := `Init.Data.UInt.Lemmas
  -- Primary file: the REAL selected native FnBody, never reconstructed from JSON.
  compactAndExport #[body] `UIntCollectorBodyCanary
    (metadata "Array IR.FnBody" source linear.size) (outputPrefix ++ ".body.jsonl")
  -- Declaration gives a stack-safe independent projection of full checking IR.
  compactAndExport #[selected.decl] `UIntCollectorBodyCanaryDecl
    (metadata "Array IR.Decl" source linear.size) (outputPrefix ++ ".decl.jsonl")
  -- Native ToJson result and native dependency list as object DAGs avoid a deep
  -- JSON string parser/recursive equality requirement in the later JVM canary.
  let expected := #[toJson selected.decl, Json.arr (linear.map encodeName)]
  compactAndExport expected `UIntCollectorBodyCanaryExpected
    (metadata "Array Lean.Json [IR.Decl, Array Name]" source linear.size) (outputPrefix ++ ".expected.jsonl")
  -- Keep the genuine imported selector Environment/region provenance alive
  -- until all borrowed compact/save/export operations are complete.
  unless !env.header.isModule && env.header.imports.size == 2 do
    throw <| IO.userError "Selector Environment changed during export"
  IO.println <| (Json.mkObj [("scope", toJson "native-actual-UInt-selected-body-canary"),
    ("selectedName", encodeName culprit), ("sourceModule", encodeName source),
    ("rootFdecl", toJson true), ("missing", toJson witness.missingDependencies.size),
    ("sorry", toJson false), ("dependencyCount", toJson linear.size),
    ("nativeCollectorParity", toJson true)]).compress

end UIntCollectorBodyCanary

-- Explicit command execution only, in a separate fresh guarded native process.
-- Prefix is deliberately fixed to a fresh candidate directory checked by script.
#eval (show IO Unit from do
  let outputDirectory := (← IO.getEnv "ANSATZ_UINT_CANARY_OUTPUT").getD "target/actual-uint-body-canary"
  UIntCollectorBodyCanary.run (outputDirectory ++ "/uint-macro"))
