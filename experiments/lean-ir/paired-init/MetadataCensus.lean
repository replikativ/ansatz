import Lean

open Lean
namespace MatchedInitMetadata

-- Exact pinned private records, as in the separately reviewed Prelude producer.
structure ImportedModuleView extends EffectiveImport where
  parts : Array (ModuleData × CompactedRegion)
  irParts : Array (ModuleData × CompactedRegion)
  needsIRTrans : Bool
structure ImportStateView where
  moduleNameMap : Std.HashMap Name ImportedModuleView
  moduleNames : Array Name

private def nameJson : Name → Json
  | .anonymous => toJson #["anonymous"]
  | .str p s => Json.arr #[toJson "str", nameJson p, toJson s]
  | .num p n => Json.arr #[toJson "num", nameJson p, toJson (toString n)]
private def importJson (i : Import) : Json := Json.mkObj [
  ("module", nameJson i.module), ("importAll", toJson i.importAll),
  ("isExported", toJson i.isExported), ("isMeta", toJson i.isMeta)]
private def partJson (d : ModuleData) (r : CompactedRegion) : Json := Json.mkObj [
  ("file", toJson r.filePath.toString), ("mappedBytes", toJson r.size.toNat),
  ("isModule", toJson d.isModule), ("imports", toJson (d.imports.map importJson)),
  ("constantCount", toJson d.constants.size), ("constNamesCount", toJson d.constNames.size),
  ("extraNames", toJson d.extraConstNames.size),
  ("extensions", toJson (d.entries.map fun (n, es) => Json.mkObj [
    ("name", nameJson n), ("entries", toJson es.size)]))]
private def selected (m : ImportedModuleView) : Except String (Nat × ModuleData) := do
  unless m.hasData do throw "logical Init module has no data"
  let some publicData := m.parts[0]? | throw "missing public part"
  let i := if publicData.1.isModule && m.importAll then 2 else 0
  let some p := m.parts[i]? | throw "missing selected part"
  return (i, p.1)
private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

unsafe def census : IO Json := do
  unless Lean.githash == "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" do
    throw <| IO.userError "wrong Lean source build"
  -- Actual empty ordinary legacy source header supplies its implicit imports.
  let input := Parser.mkInputContext "" "OrdinaryInitCensus.lean"
  let (header, _, messages) ← Parser.parseHeader input
  unless !messages.hasErrors && !Elab.HeaderSyntax.isModule header do
    throw <| IO.userError "ordinary header parse failed"
  let requests := Elab.HeaderSyntax.imports header
  let expected : Array Import := #[{module := `Init}, {module := `Init, isMeta := true}]
  unless requests == expected do throw <| IO.userError "default Init request differs"
  let (_, state) ← (importModulesCore (globalLevel := .private) requests).run
  let view : ImportStateView := unsafeCast state
  unless view.moduleNames.back? == some `Init do throw <| IO.userError "closure does not end at Init"
  let mut modules := #[]
  let mut names : Std.HashMap Name (Name × Nat × String) := {}
  let mut display : Std.HashMap String Name := {}
  let mut duplicates := #[]
  let mut collisions := #[]
  let mut occurrences := 0
  let mut mapped := 0
  let mut partsCount := 0
  let mut kinds : Std.HashMap String Nat := {}
  for moduleName in view.moduleNames do
    let some mod := view.moduleNameMap[moduleName]? | throw <| IO.userError "module absent from map"
    unless mod.module == moduleName do throw <| IO.userError "module identity mismatch"
    let (partIndex, data) ← IO.ofExcept <| selected mod
    unless data.constants.size == data.constNames.size do throw <| IO.userError "CI/name cardinality mismatch"
    for h : i in [:data.constants.size] do
      let ci := data.constants[i]
      unless data.constNames[i]? == some ci.name do throw <| IO.userError "CI/name order mismatch"
      let k := kind ci
      kinds := kinds.insert k ((kinds[k]?).getD 0 + 1)
      if let some (previousModule, previousIndex, previousKind) := names[ci.name]? then
        duplicates := duplicates.push <| Json.mkObj [
          ("name", nameJson ci.name), ("previousModule", nameJson previousModule),
          ("previousIndex", toJson previousIndex), ("previousKind", toJson previousKind),
          ("module", nameJson moduleName), ("index", toJson i), ("kind", toJson k)]
      else names := names.insert ci.name (moduleName, i, k)
      if let some other := display[ci.name.toString]? then
        unless other == ci.name do collisions := collisions.push <| Json.mkObj [
          ("left", nameJson other), ("right", nameJson ci.name)]
      else display := display.insert ci.name.toString ci.name
    occurrences := occurrences + data.constants.size
    for (_, r) in mod.parts ++ mod.irParts do mapped := mapped + r.size.toNat
    partsCount := partsCount + mod.parts.size + mod.irParts.size
    modules := modules.push <| Json.mkObj [
      ("module", nameJson moduleName), ("effectiveImport", importJson mod.toImport),
      ("hasData", toJson mod.hasData), ("irPhases", toJson (reprStr mod.irPhases)),
      ("needsIRTrans", toJson mod.needsIRTrans), ("selectedPart", toJson partIndex),
      ("parts", toJson (mod.parts.map fun (d, r) => partJson d r)),
      ("irParts", toJson (mod.irParts.map fun (d, r) => partJson d r))]
  return Json.mkObj [
    ("schema", toJson "matched-default-init-metadata-census/1"),
    ("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
    ("header", toJson ""), ("isModule", toJson false),
    ("requestedImports", toJson (requests.map importJson)), ("globalLevel", toJson "private"),
    ("moduleCount", toJson modules.size), ("partCount", toJson partsCount),
    ("selectedOccurrences", toJson occurrences), ("uniqueNames", toJson names.size),
    ("kindOccurrences", Json.mkObj (kinds.toList.map fun (k, v) => (k, toJson v))),
    ("mappedBytes", toJson mapped), ("duplicates", toJson duplicates),
    ("displayCollisions", toJson collisions), ("modules", toJson modules),
    ("nativeEnvironmentFinalized", toJson false), ("importedProofsChecked", toJson false)]
end MatchedInitMetadata

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  IO.println (← MatchedInitMetadata.census).compress
