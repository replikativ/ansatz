-- Lean 4.33.1: Lean/Meta/Eqns.lean getEqnsFor? and getUnfoldEqnFor?.
-- Ask Lean itself to realize equations, including equations of recursive
-- dependencies introduced by equation proofs. Use the exporter's own traversal
-- to determine the closure (including mutual inductives and recursor rules).
import Export
open Lean Meta

def realizeEquations (names : Array Name) : MetaM (Array Name) := do
  let mut equations := #[]
  let simp ← getSimpTheorems
  for name in names do
    if let some thms := simp.toUnfoldThms.find? name then
      equations := equations ++ thms
    if let some (.defnInfo info) := (← getEnv).find? name then
      if info.safety == .safe && (← isRecursiveDefinition name) then
        let some eqn ← getUnfoldEqnFor? name
          | throwError "No unfold equation for recursive definition `{name}`"
        let some eqns ← getEqnsFor? name
          | throwError "No equations for recursive definition `{name}`"
        equations := equations.push eqn ++ eqns
  return equations

partial def exportWithEquations (env : Environment) (roots : Array Name)
    (processed : NameHashSet := {}) : IO Unit := do
  let handle ← IO.FS.Handle.mk "/dev/null" .write
  let state ← IO.withStdout (.ofHandle handle) <|
    StateT.run' (s := {}) <| ReaderT.run (r := ({ env } : _root_.Context)) do
      initState env ["--export-unsafe"]
      for root in roots do dumpConstant root
      get
  let names := state.visitedConstants.toArray.qsort Name.quickLt
  let pending := names.filter (!processed.contains ·)
  if pending.isEmpty then
    M.run env do
      initState env ["--export-unsafe"]
      dumpMetadata
      for root in roots do
        modify fun st => { st with noMDataExprs := {} }
        dumpConstant root
  else
    let (equations, coreState) ← (realizeEquations pending).run' |>.toIO
      { fileName := "<bundle-equations>", fileMap := default }
      { env := env }
    -- Lean/Compiler/CSimpAttr.lean replaceConstant? and ImplementedByAttr.lean
    -- getImplementedBy?: companion targets are dependencies too. Preserve their
    -- safety annotations; ansatz rechecks non-safe groups with Lean's rules.
    let mut targets := #[]
    for name in pending do
      if let some entry := (Compiler.CSimp.ext.getState env).map.find? name then
        targets := targets.push entry.toDeclName
      if let some target := Compiler.getImplementedBy? env name then
        targets := targets.push target
    exportWithEquations coreState.env (roots ++ equations ++ targets)
      (pending.foldl (fun seen name => seen.insert name) processed)

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  -- Elab/Import.lean processHeaderCore loads the extensions used by equation proofs.
  enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  let roots ← args.toArray.mapM fun raw => do
    let some name := Syntax.decodeNameLit ("`" ++ raw)
      | throw <| IO.userError s!"Invalid root: {raw}"
    return name
  exportWithEquations env roots
