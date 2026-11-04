import Lean.Environment
import Lean.Util.Path
import Lean.Data.Json
open Lean
private partial def nameJson : Name → Json
  | .anonymous => toJson (["anonymous"] : List String)
  | .str p s => Json.arr #[toJson "str", nameJson p, toJson s]
  | .num p n => Json.arr #[toJson "num", nameJson p, toJson (toString n)]
def main (args : List String) : IO Unit := do
  let [root] := args | throw (IO.userError "Expected root module")
  initSearchPath (← findSysroot)
  let mut pending := #[root.toName]
  let mut seen : NameSet := {}
  let mut modules := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name || name.getRoot == `Init then continue
    unless seen.size < 128 do throw (IO.userError "Module bound")
    seen := seen.insert name
    let path ← findOLean name
    let (data, _) ← readModuleData path
    let imports := data.imports.map (·.module)
    modules := modules.push <| Json.mkObj [("module", nameJson name), ("olean", toJson path.toString),
      ("isModule", toJson data.isModule), ("imports", toJson (imports.map nameJson))]
    pending := pending ++ imports
  IO.println (Json.mkObj [("schema", toJson "lean-lake-product-inventory/1"),
    ("leanCommit", toJson Lean.githash), ("leanVersion", toJson Lean.versionString),
    ("modules", Json.arr modules)]).compress
