-- Module + docstring dumper: for every constant of the imported modules, emit NDJSON
--   {"name":"Nat.add_comm","module":"Init.Data.Nat.Basic","doc":"..."}   (doc omitted when absent)
-- Neither fact is in the kernel export (lean4export), and both are what a library user
-- searches by: the catalogue (ansatz.catalogue) stores them as :decl/module and :decl/doc.
-- Run with the SAME toolchain that produced the export, where the module is importable:
--   cd ../mathlib4 && lake env lean --run ../ansatz/scripts/dump_modules.lean Mathlib \
--     | gzip -c > ../ansatz/test-data/mathlib-modules.ndjson.gz
-- (Defaults to Init when no module args are given.)
import Lean
open Lean

def dumpModules : CoreM Unit := do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    let modName := match env.getModuleIdxFor? n with
      | some idx => toString (env.header.moduleNames[idx.toNat]!)
      | none => "<current>"
    let doc ← findDocString? env n
    let fields : List (String × Json) :=
      [("name", Json.str (toString n)), ("module", Json.str modName)]
      ++ (match doc with | some d => [("doc", Json.str d)] | none => [])
    IO.println (Json.mkObj fields).compress

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let modNames := if args.isEmpty then ["Init"] else args
  let mods := modNames.toArray.map (fun m => ({ module := m.toName } : Import))
  let env ← importModules mods {}
  let _ ← dumpModules.toIO { fileName := "<dump_modules>", fileMap := default } { env := env }
  pure ()
