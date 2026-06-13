-- Standalone attribute dumper: emit the @[simp] lemma + unfold names of the imported
-- Lean modules as NDJSON (one object per line), so ansatz can inherit Lean's own simp set
-- as an Env extension. Run with the SAME toolchain that produced the kernel export, e.g.
--   lean --run scripts/dump_attrs.lean Init > /tmp/init-attrs.ndjson
-- (Defaults to Init when no module args are given.)
import Lean
open Lean Meta

def dumpSimp : CoreM Unit := do
  let some ext ← getSimpExtension? `simp
    | throwError "no `simp` extension registered"
  let env ← getEnv
  let nMods := env.header.moduleNames.size
  let mut nSimp := 0
  let mut nUnfold := 0
  -- The imported scoped-extension entries live per-module (getState only sees activated scopes,
  -- which importModules doesn't activate). Fold the raw imported entries instead.
  for modIdx in [0:nMods] do
    for entry in ext.ext.getModuleEntries env modIdx do
      let e? := match entry with
        | .global e => some e
        | .scoped _ e => some e
      match e? with
      | some (.thm t) =>
        match t.origin with
        | .decl n _ _ => IO.println ("{\"kind\":\"simp\",\"name\":\"" ++ toString n ++ "\"}"); nSimp := nSimp + 1
        | _ => pure ()
      | some (.toUnfold n) =>
        IO.println ("{\"kind\":\"unfold\",\"name\":\"" ++ toString n ++ "\"}"); nUnfold := nUnfold + 1
      | _ => pure ()
  IO.eprintln s!"[diag] modules: {nMods}, simp: {nSimp}, unfold: {nUnfold}"

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let modNames := if args.isEmpty then ["Init"] else args
  let mods := modNames.toArray.map (fun m => ({ module := m.toName } : Import))
  let env ← importModules mods {}
  let _ ← dumpSimp.toIO { fileName := "<dump_attrs>", fileMap := default } { env := env }
  pure ()
