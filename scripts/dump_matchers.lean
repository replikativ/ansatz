-- Standalone matcher-info dumper: emit Lean's `Match.MatcherInfo` for every compiled `match_N`
-- auxiliary as NDJSON (one object per line), so ansatz can inherit Lean's matcher metadata
-- (numParams/numDiscrs/altInfos/uElimPos/discrInfos/overlaps) as an Env extension — needed for the
-- faithful `split` tactic on matchers (Lean's applyMatchSplitter). This metadata is NOT in the
-- kernel export (lean4export emits only types + values). Run with the SAME toolchain that produced
-- the kernel export:
--   cd ../lean4export && lake env lean --run ../ansatz/scripts/dump_matchers.lean Init > /tmp/init-matchers.ndjson
-- (Defaults to Init when no module args are given.) For Mathlib, run where Mathlib is importable and
-- drop the gzipped result into the store dir as <store>/matchers.ndjson.gz.
--
-- Lines (one per matcher):
--   {"name":"List.filter.match_1","numParams":0,"numDiscrs":1,"uElimPos":0,
--    "discrs":[null],"overlaps":[],
--    "alts":[{"numFields":0,"numOverlaps":0,"unitThunk":true},
--            {"numFields":0,"numOverlaps":0,"unitThunk":true}]}
import Lean
open Lean Meta Match

def jBool (b : Bool) : String := if b then "true" else "false"

def jAlt (a : AltParamInfo) : String :=
  "{\"numFields\":" ++ toString a.numFields ++
  ",\"numOverlaps\":" ++ toString a.numOverlaps ++
  ",\"unitThunk\":" ++ jBool a.hasUnitThunk ++ "}"

def jDiscr (d : DiscrInfo) : String :=
  match d.hName? with
  | some n => "\"" ++ toString n ++ "\""
  | none   => "null"

def jOverlaps (o : Overlaps) : String :=
  -- emit as a flat list of [overlapping,overlapped] pairs; empty for non-overlapping matchers
  let pairs := o.map.toList.flatMap (fun (k, vs) => vs.toArray.toList.map (fun v => (v, k)))
  "[" ++ String.intercalate "," (pairs.map (fun (a, b) => "[" ++ toString a ++ "," ++ toString b ++ "]")) ++ "]"

def emit (name : Name) (info : MatcherInfo) : IO Unit := do
  let alts := "[" ++ String.intercalate "," (info.altInfos.toList.map jAlt) ++ "]"
  let discrs := "[" ++ String.intercalate "," (info.discrInfos.toList.map jDiscr) ++ "]"
  let uElim := match info.uElimPos? with | some p => toString p | none => "null"
  IO.println <|
    "{\"name\":\"" ++ toString name ++ "\"" ++
    ",\"numParams\":" ++ toString info.numParams ++
    ",\"numDiscrs\":" ++ toString info.numDiscrs ++
    ",\"uElimPos\":" ++ uElim ++
    ",\"discrs\":" ++ discrs ++
    ",\"overlaps\":" ++ jOverlaps info.overlaps ++
    ",\"alts\":" ++ alts ++ "}"

-- The matcher info lives in a SimplePersistentEnvExtension (Match.Extension.extension). getState only
-- sees the local env; fold the raw per-module imported entries (like dump_attrs does for simp).
def dumpMatchers : CoreM Unit := do
  let env ← getEnv
  for modIdx in [0:env.header.moduleNames.size] do
    for e in Match.Extension.extension.getModuleEntries env modIdx do
      emit e.name e.info

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let modNames := if args.isEmpty then ["Init"] else args
  let mods := modNames.toArray.map (fun m => ({ module := m.toName } : Import))
  let env ← importModules mods {}
  let _ ← dumpMatchers.toIO { fileName := "<dump_matchers>", fileMap := default } { env := env }
  pure ()
