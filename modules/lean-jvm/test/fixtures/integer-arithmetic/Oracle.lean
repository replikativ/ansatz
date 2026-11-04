import Main

def main : IO Unit := do
  for i in [0:tableCount 0] do
    for r in [0:rowCount i 0] do
      IO.print (row i r 0)
