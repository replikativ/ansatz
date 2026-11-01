import Projection
import InitScalarCensus

open MatchedPreludeProducer

open Lean

namespace MatchedInitProducer

-- Native-only producer. The mirrored private records have exactly the field
-- order/types of pinned Lean.Environment.ImportedModule/ImportState. This avoids
-- finalizing a native Environment or exporting its callback/native-code state.
-- Do not use these unsafe views against another Lean commit.
structure ImportedModuleView extends EffectiveImport where
  parts : Array (ModuleData × CompactedRegion)
  irParts : Array (ModuleData × CompactedRegion)
  needsIRTrans : Bool

structure ImportStateView where
  moduleNameMap : Std.HashMap Name ImportedModuleView
  moduleNames : Array Name

@[export module_data_transport_mpz_repr]
unsafe def mpzRepr (value : NonScalar) : String :=
  toString (unsafeCast value : Int)

@[extern "module_data_transport_export"]
private unsafe opaque exportDAG
  (roots : @& Array ModuleData) (metadata : @& String) (path : @& String)
  (verify : Bool) : IO String

private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str parent part => Json.arr #[toJson "str", encodeName parent, toJson part]
  | .num parent part => Json.arr #[toJson "num", encodeName parent, toJson (toString part)]

private def importJson (i : Import) : Json := Json.mkObj [
  ("module", encodeName i.module), ("importAll", toJson i.importAll),
  ("isExported", toJson i.isExported), ("isMeta", toJson i.isMeta)]

private def headerJson (region : CompactedRegion) : IO Json := do
  let bytes ← IO.FS.withFile region.filePath .read fun h => h.read 88
  unless bytes.size == 88 && bytes[0]! == 111 && bytes[1]! == 108 && bytes[2]! == 101 &&
      bytes[3]! == 97 && bytes[4]! == 110 && bytes[5]! == 2 do
    throw <| IO.userError s!"ModuleDataTransport requires v2 olean: {region.filePath}"
  let version := String.fromUTF8! <| bytes.extract 7 40
  let commit := String.fromUTF8! <| bytes.extract 40 80
  unless version.startsWith "4.33.1" && commit == Lean.githash do
    throw <| IO.userError s!"ModuleDataTransport artifact build mismatch: {region.filePath}"
  return Json.mkObj [("oleanVersion", toJson bytes[5]!.toNat),
    ("oleanFlags", toJson bytes[6]!.toNat), ("leanCommit", toJson commit),
    ("filePath", toJson region.filePath.toString), ("mappedBytes", toJson region.size.toNat)]

-- ParametricAttribute Name exports Array (Name × Name), in preserved order.
-- Read requirements only; native availability and execution are not observed.
private unsafe def initEntries (data : ModuleData) : Array Json := Id.run do
  let mut result := #[]
  for (name, entries) in data.entries do
    if name == ``regularInitAttr || name == ``builtinInitAttr then
      let pairs : Array (Name × Name) := unsafeCast entries
      for (decl, initializer) in pairs do
        result := result.push <| Json.mkObj [("attribute", encodeName name),
          ("decl", encodeName decl), ("initializer", encodeName initializer)]
  return result

private unsafe def moduleDataJson (data : ModuleData) : Json := Json.mkObj [
  ("isModule", toJson data.isModule), ("initializerEntries", toJson (initEntries data)), ("imports", toJson (data.imports.map importJson)),
  ("constantCount", toJson data.constants.size), ("constNamesCount", toJson data.constNames.size),
  ("extraConstNamesCount", toJson data.extraConstNames.size),
  ("extensions", toJson (data.entries.map fun (name, entries) => Json.mkObj [
    ("name", encodeName name), ("entryCount", toJson entries.size)]))]

private unsafe def partJson (data : ModuleData) (region : CompactedRegion) (rootIndex : Nat) : IO Json := do
  return Json.mkObj [("rootIndex", toJson rootIndex), ("artifact", ← headerJson region),
    ("moduleData", moduleDataJson data)]

private def phasesJson : IRPhases → Json
  | .runtime => toJson "runtime"
  | .comptime => toJson "comptime"
  | .all => toJson "all"

private def metadata (imports : Array Import) (closure : Bool) (modules : Array Json)
    (globalLevel : OLeanLevel := .private) : Json :=
  Json.mkObj [("schema", toJson "lean-module-data-input/1"),
    ("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
    ("requestedImports", toJson (imports.map importJson)), ("transitiveClosure", toJson closure),
    ("globalLevel", toJson (match globalLevel with | .exported => "exported" | .server => "server" | .private => "private")), ("modules", toJson modules),
    ("nativeEnvironmentFinalized", toJson false),
    ("regionAddressesTransported", toJson false)]


-- Exact pinned Kernel.Environment layout; only a temporary exporter carrier.
-- This unsafe view is never serialized or returned as an imported environment.
private structure ExportKernelCarrier where
  constants : ConstMap
  quotInit : Bool
  diagnostics : Kernel.Diagnostics
  const2ModIdx : Std.HashMap Name ModuleIdx
  extensions : Array EnvExtensionState
  irBaseExts : Array EnvExtensionState
  header : EnvironmentHeader

-- Exact pinned Environment.subsumesInfo: theorem proof bodies may differ.
private def subsumesInfo (constMap : Std.HashMap Name ConstantInfo) (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.type == b.type && a.levelParams == b.levelParams &&
  match a, b with
  | .thmInfo x, .thmInfo y => x.all == y.all
  | .thmInfo x, .axiomInfo y => x.all == [y.name] && !y.isUnsafe
  | .axiomInfo x, .axiomInfo y => x.isUnsafe == y.isUnsafe && isPropCheap x.type
  | _, _ => false
where
  isPropCheap (ty : Expr) : Bool := Id.run do
    let mut ty := ty
    while ty.isForall do
      let .forallE (body := body) .. := ty | return false
      ty := body
    let .const n .. := ty.getAppFn | return false
    let some decl := constMap[n]? | return false
    let mut p := decl.type
    for _ in 0...ty.getAppNumArgs do
      let .forallE (body := body) .. := p | return false
      p := body
    p.isProp

private structure Origin where
  moduleIndex : Nat
  rootIndex : Nat
  ciIndex : Nat
private def originJson (o : Origin) : Json := Json.mkObj [
  ("moduleIndex", toJson o.moduleIndex), ("sourcePartRoot", toJson o.rootIndex),
  ("sourceCIIndex", toJson o.ciIndex)]

unsafe def produce (directory : System.FilePath) : IO Unit := do
  unless Lean.githash == "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" do
    throw <| IO.userError "wrong Lean build"
  let input := Parser.mkInputContext "" "DefaultInit.lean"
  let (header, _, messages) ← Parser.parseHeader input
  unless !messages.hasErrors && !Elab.HeaderSyntax.isModule header do
    throw <| IO.userError "ordinary header parse failed"
  let imports := Elab.HeaderSyntax.imports header
  unless imports == #[{module := `Init}, {module := `Init, isMeta := true}] do
    throw <| IO.userError "unexpected ordinary implicit imports"
  let (_, state) ← (importModulesCore (globalLevel := .private) imports).run
  let view : ImportStateView := unsafeCast state
  let mut roots : Array ModuleData := #[]
  let mut modules := #[]
  let mut map : Std.HashMap Name ConstantInfo := {}
  let mut first : Std.HashMap Name Origin := {}
  let mut winners : Std.HashMap Name Origin := {}
  let mut occurrences : Array (ConstantInfo × Origin) := #[]
  let mut ordered : Array Name := #[]
  let mut display : Std.HashMap String Name := {}
  for h : moduleIndex in [:view.moduleNames.size] do
    let moduleName := view.moduleNames[moduleIndex]
    let some mod := view.moduleNameMap[moduleName]? | throw <| IO.userError "missing module"
    unless mod.module == moduleName && mod.hasData do throw <| IO.userError "module lacks logical data"
    let some (publicData, _) := mod.parts[0]? | throw <| IO.userError "missing public part"
    let selectedIndex := if publicData.isModule && mod.importAll then 2 else 0
    let some (selectedData, _) := mod.parts[selectedIndex]? | throw <| IO.userError "missing selected part"
    let selectedRoot := roots.size + selectedIndex
    unless selectedData.constants.size == selectedData.constNames.size do
      throw <| IO.userError "CI/name count mismatch"
    for hc : ciIndex in [:selectedData.constants.size] do
      let ci := selectedData.constants[ciIndex]
      unless selectedData.constNames[ciIndex]? == some ci.name do
        throw <| IO.userError "CI/name order mismatch"
      let origin : Origin := ⟨moduleIndex, selectedRoot, ciIndex⟩
      occurrences := occurrences.push (ci, origin)
      if let some other := display[ci.name.toString]? then
        unless other == ci.name do throw <| IO.userError "display-name collision"
      else display := display.insert ci.name.toString ci.name
      let (previous, inserted) := map.getThenInsertIfNew? ci.name ci
      map := inserted
      if let some prev := previous then
        if subsumesInfo map ci prev then
          map := map.insert ci.name ci
          winners := winners.insert ci.name origin
        else unless subsumesInfo map prev ci do throw <| IO.userError s!"incompatible duplicate {ci.name}"
      else
        first := first.insert ci.name origin
        winners := winners.insert ci.name origin
        ordered := ordered.push ci.name
    let mut parts := #[]
    for (data, region) in mod.parts do
      parts := parts.push (← partJson data region roots.size)
      roots := roots.push data
    let mut irParts := #[]
    for (data, region) in mod.irParts do
      irParts := irParts.push (← partJson data region roots.size)
      roots := roots.push data
    modules := modules.push <| Json.mkObj [("module", encodeName mod.module),
      ("effectiveImport", importJson mod.toImport), ("hasData", toJson mod.hasData),
      ("irPhases", phasesJson mod.irPhases), ("needsIRTrans", toJson mod.needsIRTrans),
      ("selectedRoot", toJson selectedRoot), ("parts", toJson parts), ("irParts", toJson irParts)]
  unless view.moduleNames.size == 631 && roots.size == 3155 &&
      occurrences.size == 66124 && map.size == 65994 do
    throw <| IO.userError "pinned default Init census mismatch"
  -- Audit the complete winning inventory using the generic source family checks.
  -- The Prelude-only audit function has a fixed count, so repeat its checks here.
  for (ci, _) in occurrences do
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? true then deps := deps ++ value.getUsedConstants
    let mut family : List Name := []
    match ci with
    | .defnInfo v => family := v.all
    | .thmInfo v => family := v.all
    | .opaqueInfo v => family := v.all
    | .inductInfo v =>
      family := v.all ++ v.ctors
      for ctor in v.ctors do
        unless (map[ctor]?).any (fun c => match c with | .ctorInfo c => c.induct == v.name | _ => false) do
          throw <| IO.userError "incomplete constructor family"
    | .ctorInfo v =>
      family := [v.induct]
      unless (map[v.induct]?).any (fun c => match c with | .inductInfo i => i.ctors.contains v.name | _ => false) do
        throw <| IO.userError "orphan constructor"
    | .recInfo v =>
      family := v.all ++ v.rules.map (·.ctor)
      for r in v.rules do deps := deps ++ r.rhs.getUsedConstants
    | _ => pure ()
    for n in deps ++ family do
      unless map.contains n do throw <| IO.userError s!"unresolved dependency {ci.name} -> {n}"
  for n in [`Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
    unless (map[n]?).any (fun c => match c with | .quotInfo _ => true | _ => false) do
      throw <| IO.userError "missing genuine quotient"
  let sourceMetadata := metadata imports true modules
  IO.FS.writeFile (directory / "source-metadata.json") sourceMetadata.compress
  IO.eprintln "source selection complete; exporting native DAG without clone verification"
  let receipt ← exportDAG roots sourceMetadata.compress (directory / "module-data.jsonl").toString false
  IO.FS.writeFile (directory / "transport-receipt.json") receipt
  IO.eprintln "native DAG complete; exporting typed scalar claims"
  scalarCensus roots (directory / "typed-scalars.json").toString
  let empty ← mkEmptyEnvironment
  let carrier : ExportKernelCarrier := unsafeCast empty.toKernelEnv
  let carrier := {carrier with constants := SMap.fromHashMap map false, quotInit := true}
  let env := Environment.ofKernelEnv (unsafeCast carrier)
  IO.eprintln "typed scalar claims complete; exporting kernel DAG"
  IO.FS.withFile (directory / "kernel.ndjson") .write fun output => do
    IO.withStdout (.ofHandle output) do
      M.run env do
        initState env ["--export-unsafe"]
        modify fun st => {st with visitedExprs := Std.HashMap.emptyWithCapacity 1048576}
        dumpMetadata
        for name in ordered do dumpConstant name
        unless (← get).visitedConstants.size == map.size do
          throw <| IO.userError "exporter domain mismatch"
        let out ← IO.FS.Handle.mk (directory / "correspondence.jsonl") .write
        out.putStrLn (Json.mkObj [("schema", toJson "matched-default-init-source-correspondence/1"),
          ("quotInit", toJson true), ("bodyPolicy", toJson "full"),
          ("constantCount", toJson map.size), ("occurrenceCount", toJson occurrences.size),
          ("normalization", toJson "lean4export MData erasure and let.nonDep=false")]).compress
        for (ci, origin) in occurrences do
          let some winner := winners[ci.name]? | throw <| IO.userError "missing winner"
          let some attributed := first[ci.name]? | throw <| IO.userError "missing first origin"
          out.putStrLn (Json.mkObj [("typedName", typedName ci.name),
            ("displayName", toJson ci.name.toString), ("source", originJson origin),
            ("winner", originJson winner), ("firstAttribution", originJson attributed),
            ("selected", toJson (origin.moduleIndex == winner.moduleIndex && origin.ciIndex == winner.ciIndex)),
            ("shape", ← checkingShape ci)]).compress
  IO.eprintln "paired default Init export complete; no native Environment finalization performed"
end MatchedInitProducer
unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [directory] =>
    initSearchPath (← findSysroot)
    MatchedInitProducer.produce directory
    return 0
  | _ => throw <| IO.userError "usage: MatchedInitProducer EXISTING_EMPTY_OUTPUT_DIRECTORY"
