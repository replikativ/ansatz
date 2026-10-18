-- Fail before export if any requested public root is absent. lean4export's
-- panic! diagnostic can return exit status zero, so process status is insufficient.
import Lean
open Lean

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {}
  let mut missing : Array Json := #[]
  for path in args do
    for raw in (← IO.FS.readFile path).splitOn "\n" do
      let line := raw.trimAscii.toString
      if line.isEmpty || line.startsWith "#" then continue
      let some name := Syntax.decodeNameLit ("`" ++ line)
        | throw <| IO.userError s!"Invalid requested declaration name: {line}"
      if !env.contains name then missing := missing.push (Json.str line)
  IO.println (Json.mkObj [("missing", Json.arr missing)]).compress
  return if missing.isEmpty then 0 else 1
