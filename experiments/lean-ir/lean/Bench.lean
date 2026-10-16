import Init

mutual
  @[noinline] def bounceA (n acc : Nat) : Nat :=
    match n with
    | 0 => acc
    | n+1 => bounceB n (acc+1)
  @[noinline] def bounceB (n acc : Nat) : Nat :=
    match n with
    | 0 => acc
    | n+1 => bounceA n (acc+1)
end

mutual
  @[noinline] partial def wordA (n acc : UInt64) : UInt64 :=
    if n == 0 then acc else wordB (n-1) (acc+1)
  @[noinline] partial def wordB (n acc : UInt64) : UInt64 :=
    if n == 0 then acc else wordA (n-1) (acc+1)
end

@[noinline] def runMap (xs : List Nat) : List Nat := xs.map (· + 1)

-- Opaque call boundaries keep pure computation inside the timed IO interval.
@[noinline] def mapIO (xs : List Nat) : IO (List Nat) := pure (runMap xs)
@[noinline] def bounceIO (n : Nat) : IO Nat := pure (bounceA n 0)
@[noinline] def wordIO (n : UInt64) : IO UInt64 := pure (wordA n 0)

-- Keep a second owner observably alive across map in the shared case.
def sample (workload : String) (n : Nat) : IO (Nat × Nat) := do
  if workload == "word" then
    let input := n.toUInt64
    let before ← IO.monoNanosNow
    let result ← wordIO input
    let after ← IO.monoNanosNow
    return (after - before, result.toNat)
  else if workload == "tail" then
    let before ← IO.monoNanosNow
    let result ← bounceIO n
    let after ← IO.monoNanosNow
    return (after - before, result)
  else if workload == "unique" then
    let input := List.range n
    let before ← IO.monoNanosNow
    let result ← mapIO input
    let after ← IO.monoNanosNow
    return (after - before, result.headD 0)
  else if workload == "shared" then
    let keep ← IO.mkRef (List.range n)
    let input ← keep.get
    let before ← IO.monoNanosNow
    let result ← mapIO input
    let after ← IO.monoNanosNow
    let original ← keep.get
    if original.headD 99 != 0 then throw (IO.userError "shared input changed")
    return (after - before, result.headD 0)
  else throw (IO.userError "unknown workload")

def main (args : List String) : IO Unit := do
  let workload := args[0]!
  let n := args[1]!.toNat!
  let warmup := args[2]!.toNat!
  let count := args[3]!.toNat!
  for _ in [:warmup] do
    let _ ← sample workload n
  for _ in [:count] do
    let (elapsed, result) ← sample workload n
    IO.println s!"{elapsed} {result}"
