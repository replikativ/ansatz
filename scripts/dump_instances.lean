-- Standalone instance dumper: emit every @[instance] registration of the imported Lean modules as
-- TSV (one per line: `class<TAB>instance<TAB>priority`), so ansatz can inherit Lean's AUTHORITATIVE
-- typeclass instance registry (name-INDEPENDENT discovery; replaces PSS name-guessing). The class is
-- the head constant of the instance type's conclusion. Run where the module is importable (a lake
-- project with its oleans built):
--
--   cd ../mathlib4 && lake env lean --run ../ansatz/scripts/dump_instances.lean Mathlib \
--     > ~/.local/share/ansatz/stores/mathlib/instances.tsv
--
-- (a/init!) auto-loads `<store>/instances.tsv` (plain TSV — no gzip) into the
-- instance index. Defaults to Mathlib; pass module names as args to scope it.
import Lean
open Lean Meta

-- scoped extensions: getState only sees activated scopes, which importModules does not activate —
-- so fold the raw per-module imported entries instead (as dump_attrs does for simp).
def foldModuleEntries [Inhabited σ] (ext : PersistentEnvExtension α β σ)
    (f : α → CoreM Unit) : CoreM Unit := do
  let env ← getEnv
  for modIdx in [0:env.header.moduleNames.size] do
    for e in ext.getModuleEntries env modIdx do
      f e

-- The class an instance provides = the head constant of its type's conclusion.
partial def conclHead : Expr → Expr
  | .forallE _ _ b _ => conclHead b
  | e => e.getAppFn

def emit (entry : InstanceEntry) : CoreM Unit := do
  match entry.globalName? with
  | none => pure ()
  | some name =>
    match (← getEnv).find? name with
    | none => pure ()
    | some ci =>
      match conclHead ci.type with
      | .const className .. => IO.println s!"{className}\t{name}\t{entry.priority}"
      | _ => pure ()

def dumpInstances : CoreM Unit :=
  foldModuleEntries Lean.Meta.instanceExtension.ext fun entry =>
    match entry with
    | .global e   => emit e
    | .scoped _ e => emit e

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let modNames := if args.isEmpty then ["Mathlib"] else args
  let mods := modNames.toArray.map (fun m => ({ module := m.toName } : Import))
  let env ← importModules mods {}
  discard <| dumpInstances.toIO { fileName := "<dump_instances>", fileMap := default } { env := env }
