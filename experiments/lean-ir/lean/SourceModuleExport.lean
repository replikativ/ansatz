import Lean

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
  let data ← mkModuleData env .private
  let metadata := Json.mkObj [
    ("schema", toJson "lean-source-module/1"),
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
    ("origin", toJson "owned-guest-module-data"),
    ("initializersExecuted", toJson false), ("environmentSerialized", toJson false)]
  return (data, metadata.compress)

end SourceModuleExport
