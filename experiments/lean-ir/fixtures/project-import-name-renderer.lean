import Lean.Elab.Frontend
open Lean
private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", encodeName p, toJson s]
  | .num p n => Json.arr #[toJson "num", encodeName p, toJson (toString n)]
def cases : List (String × String × Option Name) := [
  ("keyword", "import «import»\n", some (.str .anonymous "import")),
  ("space-unicode", "import «my package».«λ界»\n", some (.str (.str .anonymous "my package") "λ界")),
  ("apostrophe", "import «foo'»\n", some (.str .anonymous "foo'")),
  ("numeric-string", "import «123»\n", some (.str .anonymous "123")),
  ("inner-open", "import «a«b»\n", some (.str .anonymous "a«b")),
  ("newline", "import «a\nb»\n", some (.str .anonymous "a\nb")),
  ("comment-looking", "import «a -- x»\n", some (.str .anonymous "a -- x")),
  ("closing-delimiter", "import «a»b»\n", none)]
def main : IO Unit := do
  unless Lean.githash == "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" do
    throw <| IO.userError "wrong Lean commit"
  for (label, text, expected) in cases do
    let (header, state, messages) ← Parser.parseHeader (Parser.mkInputContext text "ImportNameOracle.input")
    let imports := Elab.HeaderSyntax.imports header
    let exact : Bool := match expected with
      | some n => !messages.hasErrors && imports.size == 3 && imports[2]!.module == n &&
          !imports[2]!.isMeta && imports[2]!.isExported && !imports[2]!.importAll && state.pos.byteIdx == text.utf8ByteSize
      | none => messages.hasErrors || imports.size != 3 || imports[2]!.module != .str .anonymous "a»b"
    IO.println <| (Json.mkObj [("case", toJson label), ("hasErrors", toJson messages.hasErrors),
      ("headerEndByte", toJson state.pos.byteIdx), ("imports", toJson (imports.map fun i => Json.mkObj [("module", encodeName i.module), ("isMeta", toJson i.isMeta), ("isExported", toJson i.isExported), ("importAll", toJson i.importAll)])),
      ("expectedObservation", toJson exact)]).compress
    unless exact do throw <| IO.userError "unexpected parser observation"
