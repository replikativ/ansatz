import App

def nativeOracle : IO Unit := do
  IO.println (← LakeTutorial.sortNats #[3, 1, 2])
  let (sorted, original) ← LakeTutorial.sortAndOriginal #[3, 1, 2]
  IO.println s!"{sorted},{original}"

#eval nativeOracle
