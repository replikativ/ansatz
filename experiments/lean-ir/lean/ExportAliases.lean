import Lean

open Lean

private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", encodeName p, toJson s]
  | .num p n => Json.arr #[toJson "num", encodeName p, toJson (toString n)]

/-- Metadata only: an exported symbol does not promise a linked executable body. -/
unsafe def main : IO Unit := do
  if Lean.versionString != "4.33.1" then
    throw <| IO.userError "ExportAliases requires Lean 4.33.1"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Lean, importAll := true, isMeta := true }] {}
    (loadExts := true) (level := .private)
  let mut exports : Array (String × Name) := #[]
  for (name, _) in env.constants.toList do
    if let some symbol := getExportNameFor? env name then
      exports := exports.push (symbol.toString, name)
  exports := exports.qsort fun a b => if a.1 == b.1 then Name.quickLt a.2 b.2 else a.1 < b.1
  -- Pinned bootstrap canaries: MetaM implementations must remain discoverable
  -- as guest targets, including private implementation names.
  for symbol in #["lean_eval_check_meta", "lean_whnf", "lean_infer_type",
      "lean_is_expr_def_eq", "lean_is_level_def_eq", "lean_checked_assign", "lean_synth_pending"] do
    if (exports.filter fun entry => entry.1 == symbol).size != 1 then
      throw <| IO.userError s!"expected one exported target for {symbol}"
  let entries := exports.map fun (symbol, name) =>
    let sourceModule? := (env.getModuleIdxFor? name).bind fun idx =>
      (env.header.modules[idx.toNat]?).map (·.module)
    Json.mkObj [("symbol", toJson symbol), ("name", encodeName name),
      ("sourceModule", sourceModule?.map encodeName |>.getD Json.null)]
  IO.println <| (Json.mkObj [("kind", toJson "manifest"), ("schema", toJson "lean-ir-probe/1"),
    ("leanVersion", toJson Lean.versionString),
    ("leanCommit", toJson Lean.githash),
    ("producer", toJson "lean/ExportAliases.lean"),
    ("scope", toJson "all visible constants from full-visibility import Lean"),
    ("exports", Json.arr entries),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits),
      ("target", toJson System.Platform.target)]),
    ("modules", Json.arr #[])]).compress
