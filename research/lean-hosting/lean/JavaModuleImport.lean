import Lean

/- Host assembly helpers for pinned Lean 4.33.1 ModuleData. These helpers create
   guest data and call the original import finalizer. They do not associate a
   Java kernel environment or certify imported declarations.
   ImportedModuleView/ImportStateView must track Lean.Environment at commit
   819816b2e0a3bf405af45ae5c7af2491d8f5bee6; the module producer and JVM adapter
   independently authenticate the layout and source cohort. -/
open Lean
namespace JavaModuleImport

structure ImportedModuleView extends EffectiveImport where
  parts : Array (ModuleData × CompactedRegion)
  irParts : Array (ModuleData × CompactedRegion)
  needsIRTrans : Bool

structure ImportStateView where
  moduleNameMap : Std.HashMap Name ImportedModuleView
  moduleNames : Array Name

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

/-- Finalize one authenticated module closure under the original extension
callbacks. Keep ordinary ownership (leakEnv=false); module/source leases must
outlive every environment using the virtual regions. Native region FFI is never
allowed to operate on these guest-only records. -/
@[noinline] unsafe def finalize (state : ImportState) (imports : Array Import) : IO Environment := do
  enableInitializersExecution
  withImporting <| finalizeImport state imports {} 0 false true .private false

end JavaModuleImport
