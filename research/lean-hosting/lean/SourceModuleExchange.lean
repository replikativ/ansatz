import Lean

/- Original ModuleData export plus the NEW exact-Prelude graph assembly profile.
   One authenticated source overlay; no Init-prefix reinterpretation, source
   publication authority, kernel association, startup claim or native region FFI.
   Record layouts are pinned to Lean commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. -/

open Lean

namespace SourceModuleExport

private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str parent part => Json.arr #[toJson "str", encodeName parent, toJson part]
  | .num parent part => Json.arr #[toJson "num", encodeName parent, toJson (toString part)]

private def importJson (i : Import) : Json := Json.mkObj [
  ("module", encodeName i.module), ("importAll", toJson i.importAll),
  ("isExported", toJson i.isExported), ("isMeta", toJson i.isMeta)]

/-- Export one compiled classic module through the genuine persistent-extension
export callbacks. Inputs are borrowed; both returned fields are caller-owned.
This neither initializes the module nor serializes/finalizes an Environment.
The caller must separately establish successful compilation and kernel/code
admission before publishing this data as a loadable module. -/
@[noinline] def exportClassic (env : @& Environment) (expectedModule : @& Name) :
    IO (ModuleData × String) := do
  unless env.mainModule == expectedModule && expectedModule != .anonymous do
    throw <| IO.userError "source export requires the exact non-anonymous main module"
  if env.header.isModule then
    throw <| IO.userError "source export currently supports classic modules only"
  let regularInits := (regularInitAttr.ext.getState env).1
  let builtinInits := (builtinInitAttr.ext.getState env).1
  unless regularInits.isEmpty && builtinInits.isEmpty do
    throw <| IO.userError "source exchange forbids actual local initializer registrations"
  let data ← mkModuleData env .private
  for name in data.constNames ++ data.extraConstNames do
    unless !isExtern env name && (getExportNameFor? env name).isNone &&
        (Compiler.getImplementedBy? env name).isNone do
      throw <| IO.userError "source exchange forbids actual extern/export/redirect requirements"
  let metadata := Json.mkObj [
    ("schema", toJson "lean-source-module/2"),
    ("producer", toJson "SourceModuleExport.exportClassic"),
    ("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits),
      ("target", toJson System.Platform.target)]),
    ("module", encodeName expectedModule), ("moduleSystem", toJson data.isModule),
    ("level", toJson "private"), ("imports", toJson (data.imports.map importJson)),
    ("constantNames", toJson (data.constNames.map encodeName)),
    ("constantCount", toJson data.constants.size),
    ("extraConstantNames", toJson (data.extraConstNames.map encodeName)),
    ("extensions", toJson (data.entries.map fun (name, entries) => Json.mkObj [
      ("name", encodeName name), ("entryCount", toJson entries.size)])),
    ("requirementsPolicy", toJson "no-local-initializers-exports-externs-redirects/1"),
    ("localRegularInitCount", toJson regularInits.length),
    ("localBuiltinInitCount", toJson builtinInits.length),
    ("origin", toJson "owned-guest-module-data"),
    ("initializersExecuted", toJson false), ("environmentSerialized", toJson false)]
  return (data, metadata.compress)

end SourceModuleExport

open Lean

namespace SourceModuleGraphPrelude

-- Pinned private record layouts at Lean commit 819816b2. No native addresses
-- occur in owned source parts; native region FFI must never see these records.
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

@[noinline] unsafe def mkOwnedPart (data : ModuleData) (key : @& String) :
    ModuleData × CompactedRegion :=
  let region : OwnedRegionView := {
    filePath := key, size := 0, isMemoryMapped := false,
    baseAddr := 0, bufferOffset := 0, root := unsafeCast data}
  (data, unsafeCast region)

/-- Bounds for this ordinary classic owned-parts assembly only. They grant no
publication, native region, checking, or initializer authority. Name bytes charge
numeric segments conservatively as ten bytes after the small-Nat bound. -/
structure GraphLimits where
  maxModules : Nat
  maxRoots : Nat
  maxEdges : Nat
  maxDepth : Nat
  maxNames : Nat
  maxNameNodes : Nat
  maxNameBytes : Nat
  maxTotalNameBytes : Nat
  maxKeyBytes : Nat
  maxTotalKeyBytes : Nat

structure GraphPartInput where
  moduleName : Name
  data : ModuleData
  key : String

/-- Ordinary data constructors for the host bridge. These grant no checked
module/closure authority; the opaque Java-side issuer validates every input. -/
@[noinline] def mkInput (moduleName : Name) (data : ModuleData) (key : String) :
    GraphPartInput := {moduleName := moduleName, data := data, key := key}

@[noinline] def mkLimits (maxModules maxRoots maxEdges maxDepth maxNames
    maxNameNodes maxNameBytes maxTotalNameBytes maxKeyBytes maxTotalKeyBytes : Nat) :
    GraphLimits := {
      maxModules := maxModules, maxRoots := maxRoots, maxEdges := maxEdges,
      maxDepth := maxDepth, maxNames := maxNames, maxNameNodes := maxNameNodes,
      maxNameBytes := maxNameBytes, maxTotalNameBytes := maxTotalNameBytes,
      maxKeyBytes := maxKeyBytes, maxTotalKeyBytes := maxTotalKeyBytes}

structure GraphAssembly where
  state : ImportState
  imports : Array Import
  regions : Array CompactedRegion

private structure Visit where
  index : Nat
  leaving : Bool
  depth : Nat

private def ordinary (i : Import) : Bool :=
  !i.importAll && i.isExported && !i.isMeta

/-- Never render a Name before bounding its spine and strings. The initial graph
profile limits numeric segments to UInt32.max; this is narrower than Name itself
and is deliberately explicit, not silent truncation or UInt64 conversion. -/
private def checkName (name : Name) (moduleName : Bool) (limits : GraphLimits)
    (total : Nat) : Except String Nat := do
  let mut name := name
  let mut nodes := 0
  let mut bytes := 0
  let mut total := total
  let mut done := false
  while !done do
    nodes := nodes + 1
    unless nodes <= limits.maxNameNodes do throw "graph Name node bound"
    match name with
    | .anonymous =>
      if moduleName && nodes == 1 then throw "anonymous graph module"
      done := true
    | .str parent part =>
      let size := part.utf8ByteSize
      bytes := bytes + size
      total := total + size
      unless bytes <= limits.maxNameBytes && total <= limits.maxTotalNameBytes do
        throw "graph Name byte bound"
      if moduleName && (part.isEmpty || part.contains '.') then throw "nonroundtrip graph module"
      name := parent
    | .num parent value =>
      if moduleName then throw "numeric graph module segment"
      unless value <= 4294967295 do throw "graph numeric Name segment bound"
      bytes := bytes + 10
      total := total + 10
      unless bytes <= limits.maxNameBytes && total <= limits.maxTotalNameBytes do
        throw "graph Name byte bound"
      name := parent
  return total

/-- Pinned Environment.ImportedModule.mainModule? selection, preserving native
parts and flags. Classic data has only exported part; module-system data selects
private under importAll. No region is read, freed, serialized or reinterpreted. -/
private def mainData? (mod : ImportedModuleView) : Option ModuleData := do
  if !mod.hasData then return (← mod.irParts.back?).1
  let publicData := (← mod.parts[0]?).1
  let level := if publicData.isModule && mod.importAll then OLeanLevel.private else OLeanLevel.exported
  return (← mod.parts[level.ctorIdx]?).1

private def irData? (mod : ImportedModuleView) : Option ModuleData := do
  let main ← mainData? mod
  if mod.irParts.isEmpty || !main.isModule then return main
  return (← mod.irParts.back?).1

private def checkLimits (l : GraphLimits) : Except String Unit := do
  unless l.maxModules > 0 && l.maxRoots > 0 && l.maxEdges > 0 && l.maxDepth > 0 &&
      l.maxNames > 0 && l.maxNameNodes > 0 && l.maxNameBytes > 0 &&
      l.maxTotalNameBytes > 0 && l.maxKeyBytes > 0 && l.maxTotalKeyBytes > 0 do
    throw "positive graph bounds required"

/-- Internal traversal tables use total reads and explicit checked writes.
No Inhabited/get! fallback or panic entry is needed for malformed input. -/
private def graphIndex (table : Std.HashMap Name Nat) (name : Name) : Except String Nat :=
  match table[name]? with
  | some value => .ok value
  | none => .error "missing graph traversal module"

private def graphNat (table : Array Nat) (index : Nat) : Except String Nat :=
  match table[index]? with
  | some value => .ok value
  | none => .error "invalid graph traversal table index"

private def graphSet (table : Array Nat) (index value : Nat) : Except String (Array Nat) :=
  if h : index < table.size then .ok (table.set index value h)
  else .error "invalid graph traversal write index"

/-- NEW explicit `prelude; import Init.Prelude` profile. This does not accept
or reinterpret an Init prefix. Requested imports stay ordinary [false,true,false],
while the authenticated classic/private effective imports use [true,false,false].

Two-phase bounded assembly over an independently authenticated exact native
Init.Prelude-only prefixView. Host issuance/version/CI proofs remain mandatory and external.
PARTS must be EXACT dependency-first DFS closure, in actual REQUESTS order;
no arbitrary topological reordering or duplicate source module is accepted.
All validation completes BEFORE allocating any logical owned source region.

Borrow all inputs. Success owns state/imports/regions. State owns one selected
part per source module; returned regions have their own ordinary Lean owners.
Logical zero-address regions are for the guest source handlers: never call native
freeRegions/withImportModules cleanup or native region read/save with these as
logical dependencies. This helper runs no finalizer, initializer or kernel check. -/
@[noinline] unsafe def assembleClassicGraphOverPrelude
    (prefixState : @& ImportState) (parts : @& Array GraphPartInput)
    (requests : @& Array Import) (limits : @& GraphLimits) : Except String GraphAssembly := do
  checkLimits limits
  let prefixView : ImportStateView := unsafeCast prefixState
  unless prefixView.moduleNames == #[`Init.Prelude] && !parts.isEmpty &&
      prefixView.moduleNames.size + parts.size <= limits.maxModules &&
      prefixView.moduleNameMap.size == prefixView.moduleNames.size &&
      requests.size >= 2 && requests.size - 1 <= limits.maxRoots do
    throw "graph module/root inventory bound"
  let mut totalBytes := 0
  let mut prefixNames : Std.HashSet Name := {}
  let mut nativeData : Array (ModuleData × ModuleData) := #[]
  let mut nameCount := requests.size + parts.size
  let mut edges := 0
  -- Prefix module names are bounded before map lookup. CI arrays are counted
  -- before any CI/extra Name traversal or source collision-map insertion.
  for moduleName in prefixView.moduleNames do
    totalBytes ← checkName moduleName true limits totalBytes
    if prefixNames.contains moduleName then throw "duplicate native graph module"
    prefixNames := prefixNames.insert moduleName
    let some mod := prefixView.moduleNameMap[moduleName]? | throw "missing native graph module"
    totalBytes ← checkName mod.module true limits totalBytes
    unless mod.module == moduleName && mod.importAll && !mod.isExported && !mod.isMeta &&
        mod.irPhases == .all && mod.hasData && !mod.needsIRTrans do
      throw "native Prelude graph effective import profile mismatch"
    let some data := mainData? mod | throw "native graph data absent"
    let some ir := irData? mod | throw "native graph IR data absent"
    unless data.constNames.size == data.constants.size do throw "native graph CI/name count mismatch"
    nameCount := nameCount + 2 + data.constNames.size + ir.extraConstNames.size
    unless nameCount <= limits.maxNames do throw "graph Name inventory bound"
    nativeData := nativeData.push (data, ir)
  unless prefixView.moduleNames.back? == some `Init.Prelude do throw "graph prefix must be the exact native Prelude closure"
  for part in parts do
    unless !part.data.isModule && part.data.imports.size >= 1 &&
        part.data.constNames.size == part.data.constants.size do throw "invalid classic graph ModuleData"
    edges := edges + part.data.imports.size - 1
    nameCount := nameCount + part.data.imports.size + part.data.constNames.size + part.data.extraConstNames.size
    unless edges <= limits.maxEdges && nameCount <= limits.maxNames do throw "graph edge/Name inventory bound"
  let mut index : Std.HashMap Name Nat := {}
  let mut keys : Std.HashSet String := {}
  let mut keyBytes := 0
  for h : i in [:parts.size] do
    let part := parts[i]
    totalBytes ← checkName part.moduleName true limits totalBytes
    let size := part.key.utf8ByteSize
    keyBytes := keyBytes + size
    unless size <= limits.maxKeyBytes && keyBytes <= limits.maxTotalKeyBytes do throw "graph region key byte bound"
    if part.key.isEmpty || keys.contains part.key then throw "empty/duplicate graph region key"
    keys := keys.insert part.key
    if prefixNames.contains part.moduleName || index.contains part.moduleName then throw "duplicate graph module"
    index := index.insert part.moduleName i
    for request in part.data.imports do
      totalBytes ← checkName request.module true limits totalBytes
    for name in part.data.constNames do totalBytes ← checkName name false limits totalBytes
    for name in part.data.extraConstNames do totalBytes ← checkName name false limits totalBytes
  for request in requests do totalBytes ← checkName request.module true limits totalBytes
  for (data, ir) in nativeData do
    for name in data.constNames do totalBytes ← checkName name false limits totalBytes
    for name in ir.extraConstNames do totalBytes ← checkName name false limits totalBytes
  let preludeImport : Import := {module := `Init.Prelude}
  unless requests[0]? == some preludeImport do throw "graph header requires explicit ordinary Init.Prelude"
  for request in requests[1:] do
    unless ordinary request && index.contains request.module do throw "unsupported/missing graph root"
  for part in parts do
    unless part.data.imports[0]? == some preludeImport do
      throw "graph source requires explicit ordinary Init.Prelude"
    for dependency in part.data.imports[1:] do
      unless ordinary dependency && index.contains dependency.module do throw "unsupported/missing graph dependency"
  -- Name attribution is first-wins in pinned finalizeImport. Preserve native
  -- attribution as-is, then forbid ANY cross-source/native CI/extra collision.
  let mut owners : Std.HashMap Name Nat := {}
  for h : i in [:nativeData.size] do
    let (data, ir) := nativeData[i]
    for name in data.constNames do if !owners.contains name then owners := owners.insert name i
    for name in ir.extraConstNames do if !owners.contains name then owners := owners.insert name i
  for h : i in [:parts.size] do
    let part := parts[i]
    let owner := prefixView.moduleNames.size + i
    let mut localNames : Std.HashSet Name := {}
    for name in part.data.constNames do
      if localNames.contains name then throw "duplicate graph local CI name"
      localNames := localNames.insert name
      if owners.contains name then throw "graph CI attribution collision"
      owners := owners.insert name owner
    localNames := {}
    for name in part.data.extraConstNames do
      if localNames.contains name then throw "duplicate graph local extra name"
      localNames := localNames.insert name
      if let some previous := owners[name]? then
        unless previous == owner do throw "graph extra attribution collision"
      else owners := owners.insert name owner
  let mut stack : Array Visit := #[]
  for request in requests[1:].toArray.reverse do
    let position ← graphIndex index request.module
    stack := stack.push {index := position, leaving := false, depth := 1}
  let mut colors := Array.replicate parts.size 0
  let mut heights := Array.replicate parts.size 0
  let mut order : Array Nat := #[]
  while !stack.isEmpty do
    let some visit := stack.back? | throw "empty graph traversal stack"
    stack := stack.pop
    let some part := parts[visit.index]? | throw "invalid graph traversal index"
    unless visit.depth <= limits.maxDepth do throw "graph dependency depth bound"
    let color ← graphNat colors visit.index
    if visit.leaving then
      let mut height := 1
      for dependency in part.data.imports[1:] do
        let position ← graphIndex index dependency.module
        let dependencyHeight ← graphNat heights position
        height := max height (dependencyHeight + 1)
      unless visit.depth + height - 1 <= limits.maxDepth do throw "graph dependency depth bound"
      heights ← graphSet heights visit.index height
      colors ← graphSet colors visit.index 2
      order := order.push visit.index
    else if color == 1 then throw "graph dependency cycle"
    else if color == 2 then
      let height ← graphNat heights visit.index
      unless visit.depth + height - 1 <= limits.maxDepth do throw "graph dependency depth bound"
    else
      colors ← graphSet colors visit.index 1
      stack := stack.push {visit with leaving := true}
      for dependency in part.data.imports[1:].toArray.reverse do
        let position ← graphIndex index dependency.module
        stack := stack.push {index := position, leaving := false, depth := visit.depth + 1}
  unless order.size == parts.size do throw "graph parts include unselected modules"
  for h : i in [:order.size] do
    unless order[i] == i do throw "graph parts differ from ordered dependency closure"
  -- Phase two: no more validation/Except failures. Original prefix record values
  -- stay shared; the borrowed prefix state is never overwritten.
  let mut state := prefixView
  let mut regions := #[]
  for part in parts do
    let owned := mkOwnedPart part.data part.key
    let imported : ImportedModuleView := {
      module := part.moduleName, importAll := true, isExported := false, isMeta := false,
      irPhases := .all, hasData := true, parts := #[owned], irParts := #[], needsIRTrans := false}
    state := {state with moduleNameMap := state.moduleNameMap.insert part.moduleName imported,
                         moduleNames := state.moduleNames.push part.moduleName}
    regions := regions.push owned.2
  return {state := unsafeCast state, imports := requests, regions}

end SourceModuleGraphPrelude
