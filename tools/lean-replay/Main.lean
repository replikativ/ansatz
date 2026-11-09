/-
Re-check a lean4export NDJSON file in Lean 4's own kernel.

This is the Lean Kernel Arena's "official" checker
(lean-kernel-arena/checkers/official/Main.lean) with Lean core's
`Lean.Environment.replay` in place of lean4checker's copy of it: every
declaration is sent to the kernel in dependency order, and the constructors and
recursors in the file must equal the ones the kernel generates for each
inductive.

  lake exe lean-replay FILE.ndjson            -- exit 0: accepted
  lake exe lean-replay --parse-only FILE.ndjson

A rejection is an uncaught error naming the declaration (exit code 1).
-/
import Export.Parse
import Lean

def runKernel (solution : Export.ExportedEnv) : IO Unit := do
  let env ← Lean.mkEmptyEnvironment
  -- The kernel adds the whole quotient package for `Quot`; adding the other
  -- three primitives again would fail as duplicates.
  let constMap := solution.constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| env.replay constMap
  IO.println s!"Accepted {constMap.size} declarations."

def main (args : List String) : IO Unit := do
  let (inputPath, parseOnly) ← match args with
    | ["--parse-only", inputPath] => pure (inputPath, true)
    | [inputPath] => pure (inputPath, false)
    | _ => throw <| .userError "Expected input file path as first argument, optionally preceded by --parse-only."
  let handle ← IO.FS.Handle.mk inputPath .read
  let env ← Export.parseStream (.ofHandle handle)
  if parseOnly then
    IO.println s!"Parse successful: {env.constMap.size} declarations."
  else
    runKernel env
