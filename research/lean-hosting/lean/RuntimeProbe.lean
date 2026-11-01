import Init

namespace RuntimeProbe
@[noinline] def arraySize (n : Nat) : Nat := (#[n, n + 1]).size
@[noinline] def arrayList (n : Nat) : List Nat := (#[n, n + 1]).toList
@[noinline] def taskMap (n : Nat) : Nat :=
  (Task.map (fun x => x + n) (Task.pure n)).get
initialize counter : IO.Ref Nat ← IO.mkRef 40
initialize wasInitializing : Bool ← IO.initializing
@[noinline] def bump : IO Nat := do
  let n ← counter.get
  counter.set (n + 1)
  pure (n + 1)
end RuntimeProbe

def main : IO Unit := do
  IO.println (RuntimeProbe.arraySize 10)
  IO.println (RuntimeProbe.arrayList 10)
  IO.println (RuntimeProbe.taskMap 10)
  IO.println (← RuntimeProbe.bump)
  IO.println (← RuntimeProbe.bump)
