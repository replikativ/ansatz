import Projection
import ScalarCensus

open Lean

namespace MatchedPreludeProducer

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

private def moduleDataJson (data : ModuleData) : Json := Json.mkObj [
  ("isModule", toJson data.isModule), ("imports", toJson (data.imports.map importJson)),
  ("constantCount", toJson data.constants.size), ("constNamesCount", toJson data.constNames.size),
  ("extraConstNamesCount", toJson data.extraConstNames.size),
  ("extensions", toJson (data.entries.map fun (name, entries) => Json.mkObj [
    ("name", encodeName name), ("entryCount", toJson entries.size)]))]

private def partJson (data : ModuleData) (region : CompactedRegion) (rootIndex : Nat) : IO Json := do
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

/-- One native importModulesCore read supplies BOTH output roots and private CIs.
This constructs only a temporary exporter lookup carrier, never finalizeImport,
addDecl, imported proof checking, extension callbacks, or executable IR. -/
unsafe def produce (directory : System.FilePath) : IO Unit := do
  unless Lean.githash == "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" do
    throw <| IO.userError "wrong Lean build"
  let imports : Array Import := #[{module := `Init.Prelude, importAll := true}]
  let (_, state) ← (importModulesCore (globalLevel := .private) imports).run
  let view : ImportStateView := unsafeCast state
  unless view.moduleNames == #[`Init.Prelude] do
    throw <| IO.userError "expected exactly Init.Prelude closure"
  let some mod := view.moduleNameMap[`Init.Prelude]? |
    throw <| IO.userError "missing Prelude"
  unless mod.module == `Init.Prelude && mod.importAll && mod.hasData &&
      !mod.isExported && !mod.isMeta && mod.parts.size == 3 && mod.irParts.size == 2 do
    throw <| IO.userError "unexpected effective Prelude module parts"
  -- Faithful ImportedModule.mainModule? / getData? at the pinned source:
  -- hasData + importAll + public.isModule selects private part index 2.
  unless (mod.parts[0]?.map (·.1.isModule)).getD false do
    throw <| IO.userError "expected module-system Prelude"
  let some (data, _) := mod.parts[2]? | throw <| IO.userError "missing private part"
  unless data.imports.isEmpty do throw <| IO.userError "unexpected Prelude dependencies"
  auditSource data
  let mut roots : Array ModuleData := #[]
  let mut parts := #[]
  for (data, region) in mod.parts do
    parts := parts.push (← partJson data region roots.size)
    roots := roots.push data
  let mut irParts := #[]
  for (data, region) in mod.irParts do
    irParts := irParts.push (← partJson data region roots.size)
    roots := roots.push data
  let module := Json.mkObj [("module", encodeName mod.module),
    ("effectiveImport", importJson mod.toImport), ("hasData", toJson mod.hasData),
    ("irPhases", phasesJson mod.irPhases), ("needsIRTrans", toJson mod.needsIRTrans),
    ("parts", toJson parts), ("irParts", toJson irParts)]
  -- Lookup-only exporter carrier: unlike local add, imported constants must
  -- inhabit SMap.map₁ (Environment.find? reads imported map₁ directly).
  let mut map : Std.HashMap Name ConstantInfo := {}
  for ci in data.constants do map := map.insert ci.name ci
  let constants := SMap.fromHashMap map false
  let empty ← mkEmptyEnvironment
  let carrier : ExportKernelCarrier := unsafeCast empty.toKernelEnv
  let carrier := {carrier with constants, quotInit := true}
  let env := Environment.ofKernelEnv (unsafeCast carrier)
  IO.FS.withFile (directory / "kernel.ndjson") .write fun output => do
    IO.withStdout (.ofHandle output) do
      M.run env do
        initState env ["--export-unsafe"]
        -- Avoid the exporter's ten-million-entry default Expr table for Prelude.
        modify fun st => {st with visitedExprs := Std.HashMap.emptyWithCapacity 65536}
        dumpMetadata
        for ci in data.constants do dumpConstant ci.name
        let selected := (← get).visitedConstants
        unless selected.size == data.constants.size && data.constNames.all selected.contains do
          throw <| IO.userError "exporter domain differs from genuine private module inventory"
        let mut inventory := #[]
        for h : i in [:data.constants.size] do
          let ci := data.constants[i]
          inventory := inventory.push <| Json.mkObj [("sourcePartRoot", toJson (2 : Nat)),
            ("sourceCIIndex", toJson i), ("typedName", typedName ci.name),
            ("displayName", toJson ci.name.toString), ("shape", ← checkingShape ci)]
        IO.FS.writeFile (directory / "correspondence.json") <| (Json.mkObj [
          ("schema", toJson "matched-prelude-source-correspondence/1"),
          ("source", metadata imports true #[module]), ("quotInit", toJson true),
          ("bodyPolicy", toJson "full"), ("normalization", toJson "lean4export MData erasure and let.nonDep=false"),
          ("constants", toJson inventory)]).compress
  scalarCensus roots (directory / "typed-scalars.json").toString
  let receipt ← exportDAG roots (metadata imports true #[module]).compress
    (directory / "module-data.jsonl").toString true
  IO.FS.writeFile (directory / "transport-receipt.json") receipt

end MatchedPreludeProducer

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [directory] =>
    initSearchPath (← findSysroot)
    MatchedPreludeProducer.produce directory
    return 0
  | _ => throw <| IO.userError "usage: MatchedPreludeProducer EXISTING_EMPTY_OUTPUT_DIRECTORY"
