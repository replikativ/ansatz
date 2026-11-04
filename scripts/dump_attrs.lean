-- Standalone attribute dumper: emit the @[simp]/@[csimp]/@[extern]/@[implemented_by] attributes of
-- the imported Lean modules as NDJSON (one object per line), so ansatz can inherit Lean's own
-- attribute corpus as Env extensions. Run with the SAME toolchain that produced the kernel export:
--   cd ../lean4export && lean --run ../ansatz/scripts/dump_attrs.lean Init > /tmp/init-attrs.ndjson
-- (Defaults to Init when no module args are given.)
--
-- For a store LARGER than Init (e.g. Mathlib), run the dumper where that module is importable (a
-- lake project with its oleans built) and drop the gzipped result into the STORE DIR — ansatz.core
-- /init! auto-loads <store>/attrs.ndjson.gz via ansatz.attrs/load-store-attrs!:
--   cd ../mathlib4 && lake env lean --run ../ansatz/scripts/dump_attrs.lean Mathlib \
--     | gzip -c > ~/.local/share/ansatz/stores/mathlib/attrs.ndjson.gz
-- Then (a/init! "mathlib") inherits Mathlib's full @[simp] set (intersected with the store).
--
-- Lines:
--   {"kind":"simp","name":"Nat.add_zero","prio":1000}  -- a @[simp] lemma (with its priority)
--   {"kind":"unfold","name":"id"}                    -- a @[simp] def to unfold
--   {"kind":"csimp","name":"f","target":"g"}         -- @[csimp] f = g (compiler replacement)
--   {"kind":"extern","name":"Nat.add"}               -- @[extern] (externally implemented)
--   {"kind":"impl","name":"f","target":"g"}          -- @[implemented_by] f g
--   {"kind":"class","name":"BEq"}                    -- classExtension identity
import Lean
open Lean Meta Compiler

def emit (kind : String) (name : Name) (target : Option Name := none)
    (prio : Option Nat := none) (post : Option Bool := none) (inv : Option Bool := none) : IO Unit := do
  let mut fields := [("kind", Json.str kind), ("name", Json.str name.toString)]
  if let some t := target then fields := fields ++ [("target", Json.str t.toString)]
  -- The PRIORITY is load-bearing, not decoration: several of Lean's Bool lemmas are
  -- confluent only because they are `@[simp low]`. `Bool.false_eq : (false = b) = (b = false)`
  -- and `Bool.true_eq : (true = b) = (b = true)` rewrite each other's results, and only their
  -- low priority keeps `Bool.false_eq_true` / `Bool.true_eq_false` (default priority, both
  -- rewriting to `False`) winning first. A consumer that drops the priority loops.
  if let some p := prio then fields := fields ++ [("prio", toJson p)]
  if let some p := post then fields := fields ++ [("post", toJson p)]
  if let some i := inv then fields := fields ++ [("inv", toJson i)]
  IO.println (Json.mkObj fields).compress

-- Scoped extensions (simp, csimp): fold global per-module entries to exclude
-- namespace-dependent scoped rows, independent of which scopes are activated.
def foldModuleEntries [Inhabited σ] (ext : PersistentEnvExtension α β σ)
    (f : α → IO Unit) : CoreM Unit := do
  let env ← getEnv
  for modIdx in [0:env.header.moduleNames.size] do
    for e in ext.getModuleEntries env modIdx do
      f e

def dumpAttrs : CoreM Unit := do
  let excludedSimp ← IO.mkRef (0 : Nat)
  let excludedCSimp ← IO.mkRef (0 : Nat)
  -- @[simp] / @[simp]-unfold
  let some simpExt ← getSimpExtension? `simp | throwError "no `simp` extension"
  foldModuleEntries simpExt.ext fun entry => do
    match entry with
    | .scoped _ _ => excludedSimp.modify (· + 1)
    | .global e => match e with
      | .thm t => match t.origin with
        | .decl n _ inv => emit "simp" n (prio := some t.priority) (post := some t.post) (inv := some inv)
        | _ => throw <| IO.userError "global simp entry has no declaration origin"
      | .toUnfold n => emit "unfold" n
      | .toUnfoldThms n thms =>
        IO.println (Json.mkObj [("kind", Json.str "unfold-thms"), ("name", Json.str n.toString),
                               ("theorems", toJson (thms.map Name.toString))]).compress
  -- @[csimp] f = g (the Entry carries the from/to replacement)
  foldModuleEntries CSimp.ext.ext fun entry => do
    match entry with
    | .global e => emit "csimp" e.fromDeclName (some e.toDeclName)
    | .scoped _ _ => excludedCSimp.modify (· + 1)
  let stderr ← IO.getStderr
  stderr.putStrLn s!"dump_attrs: excluded scoped simp={← excludedSimp.get}, csimp={← excludedCSimp.get}"
  -- Class.lean:classExtension includes classes with no registered instances.
  -- Consume the raw imported class inventory, as for the global simp entries.
  foldModuleEntries classExtension fun entry => emit "class" entry.name
  -- @[extern] / @[implemented_by] (ParametricAttributes — getParam? works post-import)
  let env ← getEnv
  for (n, _) in env.constants.toList do
    -- Lean 4.33.1 ReducibilityAttrs.lean:getReducibilityStatus includes both
    -- core and extra extensions; kernel hints alone do not encode this status.
    let status ← getReducibilityStatus n
    let statusName := match status with
      | .reducible => "reducible"
      | .semireducible => "semireducible"
      | .irreducible => "irreducible"
      | .implicitReducible => "implicitReducible"
      | .instanceReducible => "instanceReducible"
    IO.println (Json.mkObj [("kind", Json.str "reducibility"), ("name", Json.str n.toString),
                           ("status", Json.str statusName)]).compress
    -- Meta/RecExt.lean and Meta/WHNF.lean: preserve the producer's unfolding
    -- metadata, rather than reconstructing recursion from declaration bodies.
    if recExt.isTagged env n then emit "recursive" n
    if hasSmartUnfoldingDecl env n then emit "smart-unfolding" n
    if (getExternAttrData? env n).isSome then emit "extern" n
    match getImplementedBy? env n with
    | some impl => emit "impl" n (some impl)
    | none => pure ()

unsafe def main (args : List String) : IO Unit := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let modNames := if args.isEmpty then ["Init"] else args
  let mods := modNames.toArray.map (fun m => ({ module := m.toName } : Import))
  -- Lean 4.33.1 Environment.lean:importModules defaults loadExts to false.
  -- ReducibilityAttrs.getReducibilityStatus needs the imported extra extension
  -- state as well as the core per-module entries (including global overrides).
  let env ← importModules (loadExts := true) mods {}
  let _ ← dumpAttrs.toIO { fileName := "<dump_attrs>", fileMap := default } { env := env }
  pure ()
