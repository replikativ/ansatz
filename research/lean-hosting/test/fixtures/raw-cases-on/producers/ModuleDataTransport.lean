import Lean.Environment
import Lean.Data.Json

open Lean

namespace ModuleDataTransport

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

/-- Export every actual part read by the pinned native import closure algorithm.
The native assist ends at ModuleData; guest finalizeImport/loadExts must rebuild
persistent extension states under guest runtime descriptors. No native callbacks
or finalized Environment are transported. -/
unsafe def exportClosure (imports : Array Import) (path : String) (verify := false)
    (moduleHeader := false) : IO String := do
  -- Match processHeaderCore: ordinary module headers use exported visibility;
  -- classic files use private. Server-mode imports are a separate future profile.
  let level := if moduleHeader then OLeanLevel.exported else .private
  let (_, state) ← (importModulesCore (globalLevel := level) imports).run
  let view : ImportStateView := unsafeCast state
  let mut roots : Array ModuleData := #[]
  let mut modules := #[]
  for name in view.moduleNames do
    let some mod := view.moduleNameMap[name]? |
      throw <| IO.userError s!"native import state lacks module {name}"
    unless mod.module == name do
      throw <| IO.userError "pinned ImportState view layout mismatch"
    let mut parts := #[]
    for (data, region) in mod.parts do
      parts := parts.push (← partJson data region roots.size)
      roots := roots.push data
    let mut irParts := #[]
    for (data, region) in mod.irParts do
      irParts := irParts.push (← partJson data region roots.size)
      roots := roots.push data
    modules := modules.push <| Json.mkObj [
      ("module", encodeName name), ("effectiveImport", importJson mod.toImport),
      ("hasData", toJson mod.hasData), ("irPhases", phasesJson mod.irPhases),
      ("needsIRTrans", toJson mod.needsIRTrans), ("parts", toJson parts), ("irParts", toJson irParts)]
  exportDAG roots (metadata imports true modules level).compress path verify

/-- A bounded single-module probe. Parts are read in their native dependency
chains; this deliberately does not claim a usable transitive import Environment. -/
unsafe def exportSingle (name : Name) (path : String) (verify := false) : IO String := do
  let file ← findOLean name
  let first ← readModuleData file
  let parts ← if first.1.isModule then do
      let server ← unsafe CompactedRegion.read (α := ModuleData)
        (OLeanLevel.server.adjustFileName file) #[first.2]
      let priv ← unsafe CompactedRegion.read (α := ModuleData)
        (OLeanLevel.private.adjustFileName file) #[first.2, server.2]
      pure #[first, server, priv]
    else pure #[first]
  let mut roots : Array ModuleData := #[]
  let mut rows := #[]
  for (data, region) in parts do
    rows := rows.push (← partJson data region roots.size)
    roots := roots.push data
  let irFile := file.withExtension "ir.sig"
  let irParts ← if ← irFile.pathExists then
      readModuleDataParts #[irFile, file.withExtension "ir"]
    else pure #[]
  let mut irRows := #[]
  for (data, region) in irParts do
    irRows := irRows.push (← partJson data region roots.size)
    roots := roots.push data
  let mod := Json.mkObj [("module", encodeName name), ("parts", toJson rows), ("irParts", toJson irRows)]
  exportDAG roots (metadata #[{module := name}] false #[mod]).compress path verify


-- Guest-only virtual region records retain provenance and a guest root owner.
-- Their addresses are deliberately zero: the JVM import capability, never the
-- native CompactedRegion.free/read FFI, must handle their lifetime/dependencies.
private structure VirtualRegionView where
  filePath : System.FilePath
  size : USize
  isMemoryMapped : Bool
  baseAddr : USize
  bufferOffset : USize
  root : NonScalar

@[noinline] unsafe def mkVirtualPart (data : ModuleData) (filePath : String)
    (fileBytes : USize) : ModuleData × CompactedRegion :=
  let region : VirtualRegionView := {
    filePath := filePath, size := fileBytes, isMemoryMapped := false,
    baseAddr := 0, bufferOffset := 0, root := unsafeCast data }
  (data, unsafeCast region)

@[noinline] def mkRequestedImport (moduleName : String) (importAll isExported isMeta : Bool) : Import :=
  { module := moduleName.toName, importAll, isExported, isMeta }

@[noinline] def mkImportedModule (moduleName : String) (importAll isExported isMeta : Bool)
    (phase : UInt8) (hasData needsIRTrans : Bool)
    (parts irParts : Array (ModuleData × CompactedRegion)) : ImportedModuleView :=
  { module := moduleName.toName, importAll, isExported, isMeta, hasData, needsIRTrans,
    irPhases := if phase == 0 then .runtime else if phase == 1 then .comptime else .all,
    parts, irParts }

@[noinline] unsafe def assembleImportState (modules : Array ImportedModuleView) : ImportState := Id.run do
  let mut state : ImportStateView := { moduleNameMap := {}, moduleNames := #[] }
  for mod in modules do
    state := { moduleNameMap := state.moduleNameMap.insert mod.module mod,
               moduleNames := state.moduleNames.push mod.module }
  return unsafeCast state

-- Host-facing records deliberately contain object fields only. Nat flags and
-- byte sizes avoid reproducing native scalar packing in the host adapter.
structure PartInput where
  data : ModuleData
  filePath : String
  fileBytes : Nat

structure ModuleInput where
  moduleName : String
  importAll : Nat
  isExported : Nat
  isMeta : Nat
  phase : Nat
  hasData : Nat
  needsIRTrans : Nat
  parts : Array PartInput
  irParts : Array PartInput

structure RequestInput where
  moduleName : String
  importAll : Nat
  isExported : Nat
  isMeta : Nat

/-- One guest call performs the same real constructors as the sequential host
adapter. Inputs must be validated by the host (flags 0/1, phase 0/1/2, sizes
fitting USize); no native Environment or extension state is accepted. -/
@[noinline] unsafe def batchAssemble (modules : Array ModuleInput)
    (requests : Array RequestInput) : ImportState × Array Import := Id.run do
  let mut imported := #[]
  for input in modules do
    let parts := input.parts.map fun part =>
      mkVirtualPart part.data part.filePath part.fileBytes.toUSize
    let irParts := input.irParts.map fun part =>
      mkVirtualPart part.data part.filePath part.fileBytes.toUSize
    imported := imported.push <| mkImportedModule input.moduleName
      (input.importAll == 1) (input.isExported == 1) (input.isMeta == 1)
      input.phase.toUInt8 (input.hasData == 1) (input.needsIRTrans == 1) parts irParts
  let state := assembleImportState imported
  let imports := requests.map fun input =>
    mkRequestedImport input.moduleName (input.importAll == 1)
      (input.isExported == 1) (input.isMeta == 1)
  return (state, imports)

/-- Actual guest import finalization, including persistent extension callbacks.
Requires completed guest runtime initialization, virtual-region IO adapters and
kernel environment association; this is not a native Environment shortcut.
Never call native freeRegions on the guest-only virtual region representation. -/
@[noinline] unsafe def finalizeTransport (state : ImportState) (imports : Array Import) : IO Environment := do
  enableInitializersExecution
  withImporting <| finalizeImport state imports {} 0 true true .private false

/-- Match the actual non-server header mode, including its visibility level.
A module-system call requires ModuleData collected at exported visibility;
changing only EnvironmentHeader.isModule after finalization is not equivalent. -/
@[noinline] unsafe def finalizeTransportForHeader
    (state : ImportState) (imports : Array Import) (isModule : Bool) : IO Environment := do
  enableInitializersExecution
  let level := if isModule then OLeanLevel.exported else .private
  withImporting <| finalizeImport state imports {} 0 true true level isModule

@[extern "module_data_transport_raw_nan"]
private opaque rawNaN (_ : Unit) : Float

private structure CanaryData where
  shared : Array String
  again : Array String
  bigNat : Nat
  bigInt : Int
  smallInt : Int
  ambiguousNat : Nat
  bytes : ByteArray
  floats : FloatArray
  wide : UInt64
  word : USize
  float : Float
  flag : Bool

unsafe def exportCanary (path : String) (verify : Bool) : IO String := do
  let text := "λ" ++ String.singleton (Char.ofNat 0) ++ "😀"
  let shared := #[text, text]
  let value : CanaryData := {
    shared, again := shared, bigNat := 2^200, bigInt := -(2^201 : Int),
    smallInt := -1, ambiguousNat := 4294967295,
    bytes := ⟨#[0, 255, 128]⟩,
    floats := (FloatArray.emptyWithCapacity 1).push (rawNaN ()),
    wide := 18446744073709551615, word := 18446744073709551615,
    float := rawNaN (), flag := true }
  let file : System.FilePath := path ++ ".native-v2"
  let _ ← CompactedRegion.save file `ModuleDataTransportCanary #[value, value] #[] none
  let (roots, _) ← CompactedRegion.read (α := Array CanaryData) file #[]
  let input := (metadata #[] false #[]).setObjVal! "canary" (toJson true)
  exportDAG (unsafeCast roots) input.compress path verify

unsafe def exportRejected (kind path : String) : IO String := do
  let input := (metadata #[] false #[]).compress
  if kind == "reject-closure" then
    exportDAG (unsafeCast #[(fun (n : Nat) => n + 1)]) input path false
  else if kind == "reject-external" then
    let handle ← IO.FS.Handle.mk (path ++ ".handle") .write
    exportDAG (unsafeCast #[handle]) input path false
  else
    exportDAG (unsafeCast #[(path, path.length)]) input path false

end ModuleDataTransport

unsafe def main (args : List String) : IO UInt32 := do
  let moduleHeader := args.head? == some "--module-header"
  let args := if moduleHeader then args.tail! else args
  let [mode, module, path, verify] := args |
    throw <| IO.userError "usage: ModuleDataTransport [--module-header] (single|closure) Module output.jsonl (verify|no-verify)"
  unless verify == "verify" || verify == "no-verify" do
    throw <| IO.userError "expected verify or no-verify"
  if moduleHeader && mode != "closure" then
    throw <| IO.userError "--module-header requires closure mode"
  initSearchPath (← findSysroot)
  let name := module.toName
  let result ← match mode with
    | "single" => ModuleDataTransport.exportSingle name path (verify == "verify")
    | "closure" => ModuleDataTransport.exportClosure #[{module := name, importAll := false, isExported := true}, {module := name, importAll := false, isExported := true, isMeta := true}] path (verify == "verify") moduleHeader
    | "canary" => ModuleDataTransport.exportCanary path (verify == "verify")
    | "reject-closure" | "reject-external" | "reject-heap" => ModuleDataTransport.exportRejected mode path
    | _ => throw <| IO.userError "expected single, closure, canary or reject-*"
  IO.println result
  return 0
