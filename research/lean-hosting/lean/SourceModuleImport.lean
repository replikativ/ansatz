import Lean

open Lean

namespace SourceModuleImport

-- Pinned private records from Environment.lean. Source ownership differs from
-- native compacted memory, but guest finalization consumes the actual layout.
structure ImportedModuleView extends EffectiveImport where
  parts : Array (ModuleData × CompactedRegion)
  irParts : Array (ModuleData × CompactedRegion)
  needsIRTrans : Bool

structure ImportStateView where
  moduleNameMap : Std.HashMap Name ImportedModuleView
  moduleNames : Array Name

private structure OwnedRegionView where
  filePath : System.FilePath
  size : USize
  isMemoryMapped : Bool
  baseAddr : USize
  bufferOffset : USize
  root : NonScalar

structure Assembly where
  state : ImportState
  imports : Array Import
  region : CompactedRegion

private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", encodeName p, toJson s]
  | .num p n => Json.arr #[toJson "num", encodeName p, toJson (toString n)]

/-- Actual finalizer header witness for strict projection of its quotient flag.
This is metadata, not a replacement for checking the final constant map. -/
@[noinline] def finalizerHeader (env : @& Environment) : String :=
  (Json.mkObj [("schema", toJson "lean-source-import-header/1"),
    ("producer", toJson "SourceModuleImport.finalizerHeader"),
    ("leanCommit", toJson Lean.githash), ("moduleSystem", toJson env.header.isModule),
    ("imports", toJson (env.header.imports.map fun i => Json.mkObj [
      ("module", encodeName i.module), ("importAll", toJson i.importAll),
      ("isExported", toJson i.isExported), ("isMeta", toJson i.isMeta)]))]).compress

/-- Logical source region; never pass it to native CompactedRegion FFI.
Only explicit source-registry handlers may read/free this zero-address value. -/
@[noinline] unsafe def mkOwnedPart (data : ModuleData) (key : @& String) :
    ModuleData × CompactedRegion :=
  let region : OwnedRegionView := {
    filePath := key, size := 0, isMemoryMapped := false,
    baseAddr := 0, bufferOffset := 0, root := unsafeCast data}
  (data, unsafeCast region)

/-- First bounded source-import profile: one classic module without imports.
The host separately verifies successful compilation and no initializer actions.
Effective importAll/all phases match importModulesCore at private visibility;
the actual requested header still says ordinary `import A`. -/
@[noinline] unsafe def assembleClassic (data : ModuleData) (moduleName : @& Name)
    (key : @& String) : Assembly := Id.run do
  let part := mkOwnedPart data key
  let request : Import := {module := moduleName}
  let imported : ImportedModuleView := {
    module := moduleName, importAll := true, isExported := true, isMeta := false,
    irPhases := .all, hasData := true, parts := #[part], irParts := #[], needsIRTrans := false}
  let state : ImportStateView := {
    moduleNameMap := ({} : Std.HashMap Name ImportedModuleView).insert moduleName imported,
    moduleNames := #[moduleName]}
  return {state := unsafeCast state, imports := #[request], region := part.2}

/-- Append one authenticated ordinary source module to an already assembled
native Init closure. The host authenticates the prefix, source publication and
their common world. Existing effective flags and selected parts are preserved:
the ordinary header requests both ordinary and meta Init. This is bounded
state assembly, not incremental extension of an existing Environment.

Pinned importModulesCore starts private visibility with isExported=false; the
requested header's default isExported=true is a separate field. -/
@[noinline] unsafe def appendClassicOverInit (prefixState : ImportState) (data : ModuleData)
    (moduleName : @& Name) (key : @& String) : IO Assembly := do
  let view : ImportStateView := unsafeCast prefixState
  unless !moduleName.isAnonymous && moduleName != `Init &&
      view.moduleNameMap.contains `Init && !view.moduleNameMap.contains moduleName &&
      view.moduleNames.back? == some `Init do
    throw <| IO.userError "invalid native Init prefix or conflicting source module"
  unless !data.isModule && data.imports == #[{module := `Init : Import}, {module := `Init, isMeta := true}] do
    throw <| IO.userError "source module must be classic with exactly implicit Init"
  let part := mkOwnedPart data key
  let imported : ImportedModuleView := {
    module := moduleName, importAll := true, isExported := false, isMeta := false,
    irPhases := .all, hasData := true, parts := #[part], irParts := #[], needsIRTrans := false}
  let state : ImportStateView := {
    moduleNameMap := view.moduleNameMap.insert moduleName imported,
    moduleNames := view.moduleNames.push moduleName}
  return {
    state := unsafeCast state
    imports := #[{module := `Init}, {module := `Init, isMeta := true}, {module := moduleName}]
    region := part.2
  }

/-- Actual guest finalizer. leakEnv=false matches importModules' default and
keeps owned source graphs reclaimable. No native disk/environment import occurs. -/
@[noinline] unsafe def finalizeClassic (state : ImportState) (imports : Array Import)
    (opts : @& Options) : IO Environment := do
  enableInitializersExecution
  withImporting <| finalizeImport state imports opts 0 false true .private false

end SourceModuleImport
