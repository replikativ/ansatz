import Lean.Parser.Module

namespace HeaderProbe

/-- Native parser observation; this is not a specification of the complete frontend. -/
@[noinline] def headerSummary (text : String) : IO Nat := do
  let (header, state, messages) ← Lean.Parser.parseHeader
    (Lean.Parser.mkInputContext text "HeaderProbe.input")
  return state.pos.byteIdx * 1000 + header.raw.getArgs.size * 10 +
    (if messages.hasErrors then 1 else 0)

def cases : List (String × String) := [
  ("empty", ""),
  ("import", "import Init\n"),
  ("module", "module\npublic import Init\nmeta import Lean.Parser.Module\n"),
  ("malformed", "import\n"),
  ("unicode-comments", "-- λ界\n/- α -/\nimport Init\n"),
  ("command-boundary", "import Init\ndef answer := 42\n"),
  ("invalid-public", "public import Init\n")]

end HeaderProbe

def main : IO Unit := do
  for (label, text) in HeaderProbe.cases do
    IO.println s!"{label}\t{repr text}\t{← HeaderProbe.headerSummary text}"
