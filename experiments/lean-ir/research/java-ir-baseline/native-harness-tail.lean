
@[noinline] def runCase (n : Nat) : Nat :=
  fold (fun _ v r => if v then r + 1 else r) (mkMap n) 0

def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  let repetitions := args[1]!.toNat!
  for trial in [0:7] do
    let start ← IO.monoNanosNow
    let mut checksum := 0
    for i in [0:repetitions] do
      checksum := checksum + runCase (n + i % 2)
    let stop ← IO.monoNanosNow
    IO.println s!"{trial} {n} {repetitions} {stop - start} {checksum}"
