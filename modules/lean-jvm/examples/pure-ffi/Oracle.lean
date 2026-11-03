import Main

-- Runs ordinary Lean reference definitions, with no JVM bindings involved.
def main : IO Unit := do
  IO.println (Interop.initialValue 1)
  IO.println (Interop.pipeline 41)
  let message := Interop.process 42
  IO.println s!"{message.count},{message.enabled}"
  let combined := Interop.callCombine 7
  IO.println s!"{combined.count},{combined.enabled}"
  let unicode := Interop.combine 7 true "λ😀"
  IO.println s!"{unicode.count},{unicode.enabled}"
  IO.println (Interop.callConstant 5)
  IO.println (Interop.mapped 4)
  IO.println (Interop.echo #[1, 2, 3]).toList
  IO.println (Interop.containsA "λ😀a")
  IO.println (Interop.containsA "λ😀")
