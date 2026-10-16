import Lean.Parser.Module

open Lean

private partial def syntaxJson : Syntax → Json
  | .missing => toJson "missing"
  | .node _ kind args => Json.mkObj [("kind", toJson kind.toString), ("args", Json.arr (args.map syntaxJson))]
  | .atom _ value => Json.mkObj [("atom", toJson value)]
  | .ident _ raw value _ => Json.mkObj [("ident", toJson value.toString), ("raw", toJson raw.toString)]

def main : IO Unit := do
  let samples := #["", "import Init\n", "prelude\nimport Init.Prelude\n",
                   "-- λ heading\nimport Init\ndef value := 42\n", "import\n"]
  for input in samples do
    let (stx, state, messages) ← Parser.parseHeader (Parser.mkInputContext input "<parser-oracle>")
    let diagnostics ← messages.toList.mapM (fun message => message.toString)
    IO.println <| (Json.mkObj [("input", toJson input), ("syntax", syntaxJson stx.raw),
      ("position", toJson state.pos.byteIdx), ("recovering", toJson state.recovering),
      ("hasErrors", toJson messages.hasErrors), ("diagnostics", toJson diagnostics)]).compress
