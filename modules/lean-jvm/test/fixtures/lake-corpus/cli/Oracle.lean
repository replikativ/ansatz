import App

def main : IO Unit := do
  IO.println (reprStr (CliProbe.parse ["--verbose", "input"]))
  IO.println (reprStr (CliProbe.parse ["input"]))
  IO.println (reprStr (CliProbe.parse ["--unknown", "input"]))
  let (left, right) := CliProbe.matchNumbers [1] [2, 3]
  IO.println s!"{left},{right}"
