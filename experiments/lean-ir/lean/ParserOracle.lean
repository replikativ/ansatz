import Lean.Parser.Module

open Lean

namespace ParserOracle

private partial def syntaxJson : Syntax → Json
  | .missing => toJson "missing"
  | .node _ kind args => Json.mkObj [("kind", toJson kind.toString), ("args", Json.arr (args.map syntaxJson))]
  | .atom _ value => Json.mkObj [("atom", toJson value)]
  | .ident _ raw value _ => Json.mkObj [("ident", toJson value.toString), ("raw", toJson raw.toString)]

@[noinline] def observe (input : String) : IO String := do
  let (stx, state, messages) ← Parser.parseHeader (Parser.mkInputContext input "<parser-oracle>")
  let diagnostics ← messages.toList.mapM (fun message => message.toString)
  return (Json.mkObj [("input", toJson input), ("syntax", syntaxJson stx.raw),
    ("position", toJson state.pos.byteIdx), ("recovering", toJson state.recovering),
    ("hasErrors", toJson messages.hasErrors), ("diagnostics", toJson diagnostics)]).compress

private def nameJson : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str parent value => Json.arr #[toJson "str", nameJson parent, toJson value]
  | .num parent value => Json.arr #[toJson "num", nameJson parent, toJson (toString value)]

private def rawJson (raw : Substring.Raw) : Json :=
  Json.mkObj [("string", toJson raw.str), ("start", toJson raw.startPos.byteIdx),
    ("stop", toJson raw.stopPos.byteIdx), ("text", toJson raw.toString)]

private def sourceInfoJson : SourceInfo → Json
  | .original leading pos trailing endPos => Json.mkObj [
      ("kind", toJson "original"), ("leading", rawJson leading),
      ("position", toJson pos.byteIdx), ("trailing", rawJson trailing),
      ("endPosition", toJson endPos.byteIdx)]
  | .synthetic pos endPos canonical => Json.mkObj [("kind", toJson "synthetic"),
      ("position", toJson pos.byteIdx), ("endPosition", toJson endPos.byteIdx),
      ("canonical", toJson canonical)]
  | .none => Json.mkObj [("kind", toJson "none")]

private def preresolvedJson : Syntax.Preresolved → Json
  | .namespace name => Json.mkObj [("namespace", nameJson name)]
  | .decl name fields => Json.mkObj [("declaration", nameJson name), ("fields", toJson fields)]

private partial def syntaxFullJson : Syntax → Json
  | .missing => toJson "missing"
  | .node info kind args => Json.mkObj [("kind", nameJson kind),
      ("info", sourceInfoJson info), ("args", Json.arr (args.map syntaxFullJson))]
  | .atom info value => Json.mkObj [("atom", toJson value), ("info", sourceInfoJson info)]
  | .ident info raw value preresolved => Json.mkObj [("ident", nameJson value),
      ("raw", rawJson raw), ("info", sourceInfoJson info),
      ("preresolved", toJson (preresolved.map preresolvedJson))]

/-- Additional observation profile. No baseline fixture is replaced by this data. -/
@[noinline] def observeFull (input : String) : IO String := do
  let (stx, state, messages) ← Parser.parseHeader (Parser.mkInputContext input "<parser-oracle>")
  let diagnostics ← messages.toList.mapM (fun message => message.toString)
  return (Json.mkObj [("input", toJson input), ("syntax", syntaxFullJson stx.raw),
    ("position", toJson state.pos.byteIdx), ("recovering", toJson state.recovering),
    ("hasLeading", toJson state.hasLeading),
    ("hasErrors", toJson messages.hasErrors), ("diagnostics", toJson diagnostics)]).compress

end ParserOracle

def main (args : List String) : IO Unit := do
  if args == ["--full"] then
    let samples := #["", "import Init\n", "module\npublic import Init\nmeta import Lean.Parser.Module\n",
      "import\n", "-- λ界\n/- α -/\nimport Init\n", "import Init\ndef answer := 42\n",
      "public import Init\n", "module\r\nmeta import all Lean.Parser.Module\r\n",
      "/- outer /- nested -/ λ -/\nimport Foo.«α.β»\n", "import 123\n",
      "/- unterminated λ", "\uFEFFimport Init\n"]
    for input in samples do IO.println (← ParserOracle.observeFull input)
    return
  let samples := #["", "import Init\n", "prelude\nimport Init.Prelude\n",
                   "-- λ heading\nimport Init\ndef value := 42\n", "import\n"]
  for input in samples do
    IO.println (← ParserOracle.observe input)
