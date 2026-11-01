import Lean.Elab.Frontend

namespace FrontendDiagnosticsProbe

/-- Observe collected incremental diagnostics rather than treating declaration
presence or a completed IO call as successful elaboration. -/
@[noinline] def diagnostics (text : String) : IO String := do
  let env ← Lean.mkEmptyEnvironment
  let (_, messages) ← Lean.Elab.process text env {} (some "FrontendDiagnosticsProbe.input")
  let rendered ← messages.toList.mapM fun message => message.toString
  return String.intercalate "\n" rendered

end FrontendDiagnosticsProbe

def main : IO Unit := do
  for text in ["", "namespace Hosted\nend Hosted\n"] do
    IO.println s!"input={repr text}; diagnostics={repr (← FrontendDiagnosticsProbe.diagnostics text)}"
