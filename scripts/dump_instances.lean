-- Standalone instance dumper: emit every @[instance] registration of the imported Lean modules as
-- TSV (one per line: `class<TAB>instance<TAB>priority`), so ansatz can inherit Lean's AUTHORITATIVE
-- typeclass instance registry (name-INDEPENDENT discovery; replaces PSS name-guessing). The class is
-- the class Lean indexed the instance under (see `instanceClass?`). Lines come out in MODULE (declaration)
-- order with Lean's real priorities — both are load-bearing: Lean tries instances by priority,
-- and the most recently declared first among equals (ansatz.tactic.instance/parse-instance-tsv). Run where the module is importable (a lake
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

-- The class an instance provides, found as Lean's addInstance finds it (Meta/Instances.lean,
-- checkNonClassInstance): open the type's telescope reducing, then `isClass?` on the target, so a
-- conclusion that is a reducible definition unfolding to a class counts (Mathlib v4.36's
-- instSMulDistribClassAlgEquiv), not only a syntactic class head.
-- Lean records that class when it registers the instance: the root of its discrimination-tree keys
-- is `.const <class> _`. The recorded root is used when it names a class, so a later change of an
-- alias's reducibility cannot change or lose it; otherwise the class is computed as above.
def instanceClass? (entry : InstanceEntry) (type : Expr) : CoreM (Option Name) := do
  match entry.keys[0]? with
  | some (DiscrTree.Key.const c _) =>
    if isClass (← getEnv) c then return some c
    (forallTelescopeReducing type fun _ target => isClass? target).run'
  | _ => (forallTelescopeReducing type fun _ target => isClass? target).run'

def emit (entry : InstanceEntry) : CoreM Unit := do
  match entry.globalName? with
  | none => throwError "global instance entry has no declaration name"
  | some name =>
    match (← getEnv).find? name with
    | none => throwError "global instance declaration is missing: {name}"
    | some ci =>
      match (← instanceClass? entry ci.type) with
      | some className =>
        let classText := className.toString
        let nameText := name.toString
        if [classText, nameText].any (fun text => text.toList.any (fun c => c == '\t' || c == '\r' || c == '\n')) then
          throwError "instance name cannot be represented in TSV: {name}"
        IO.println s!"{classText}\t{nameText}\t{entry.priority}"
      | none => throwError "global instance does not conclude in a class: {name}"

-- Only GLOBAL registrations: a `scoped instance` is inactive unless its namespace is opened,
-- and after `importModules` none is — emitting it would hand synthesis an instance Lean itself
-- never tries (e.g. grind's internal ring adapters).
def dumpInstances : CoreM Unit :=
  foldModuleEntries Lean.Meta.instanceExtension.ext fun entry =>
    match entry with
    | .global e   => emit e
    | .scoped _ _ => pure ()

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let modNames := if args.isEmpty then ["Mathlib"] else args
  let mods := modNames.toArray.map (fun m => ({ module := m.toName } : Import))
  -- loadExts: extension states (the class registry isClass? reads) are initialised
  -- module initializers run now and may print: keep stdout for the TSV only
  let out ← IO.setStdout (← IO.getStderr)
  let env ← importModules mods {} (loadExts := true)
  discard <| IO.setStdout out
  discard <| dumpInstances.toIO { fileName := "<dump_instances>", fileMap := default } { env := env }
