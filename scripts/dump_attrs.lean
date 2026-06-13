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
--   {"kind":"simp","name":"Nat.add_zero"}            -- a @[simp] lemma
--   {"kind":"unfold","name":"id"}                    -- a @[simp] def to unfold
--   {"kind":"csimp","name":"f","target":"g"}         -- @[csimp] f = g (compiler replacement)
--   {"kind":"extern","name":"Nat.add"}               -- @[extern] (externally implemented)
--   {"kind":"impl","name":"f","target":"g"}          -- @[implemented_by] f g
import Lean
open Lean Meta Compiler

def emit (kind : String) (name : Name) (target : Option Name := none) : IO Unit := do
  let base := "{\"kind\":\"" ++ kind ++ "\",\"name\":\"" ++ toString name ++ "\""
  IO.println (match target with
    | some t => base ++ ",\"target\":\"" ++ toString t ++ "\"}"
    | none   => base ++ "}")

-- scoped extensions (simp, csimp): getState only sees activated scopes, which importModules does
-- not activate — so fold the raw per-module imported entries instead.
def foldModuleEntries [Inhabited σ] (ext : PersistentEnvExtension α β σ)
    (f : α → IO Unit) : CoreM Unit := do
  let env ← getEnv
  for modIdx in [0:env.header.moduleNames.size] do
    for e in ext.getModuleEntries env modIdx do
      f e

def dumpAttrs : CoreM Unit := do
  -- @[simp] / @[simp]-unfold
  let some simpExt ← getSimpExtension? `simp | throwError "no `simp` extension"
  foldModuleEntries simpExt.ext fun entry => do
    match (match entry with | .global e => some e | .scoped _ e => some e) with
    | some (.thm t) => match t.origin with
      | .decl n _ _ => emit "simp" n
      | _ => pure ()
    | some (.toUnfold n) => emit "unfold" n
    | _ => pure ()
  -- @[csimp] f = g (the Entry carries the from/to replacement)
  foldModuleEntries CSimp.ext.ext fun entry => do
    let e := match entry with | .global e => e | .scoped _ e => e
    emit "csimp" e.fromDeclName (some e.toDeclName)
  -- @[extern] / @[implemented_by] (ParametricAttributes — getParam? works post-import)
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if (getExternAttrData? env n).isSome then emit "extern" n
    match getImplementedBy? env n with
    | some impl => emit "impl" n (some impl)
    | none => pure ()

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let modNames := if args.isEmpty then ["Init"] else args
  let mods := modNames.toArray.map (fun m => ({ module := m.toName } : Import))
  let env ← importModules mods {}
  let _ ← dumpAttrs.toIO { fileName := "<dump_attrs>", fileMap := default } { env := env }
  pure ()
