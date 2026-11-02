def main : IO Unit := do
  let line ← (← IO.getStdin).getLine
  IO.print line
