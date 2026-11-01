import HeapProbe

@[noinline] def listInputIO (n : Nat) : IO (List Nat) := pure (List.range n)
@[noinline] def listKernelIO (op : Nat) (xs : List Nat) : IO (Nat × List Nat) :=
  pure <| if op == 0 then (0, xs.map (· + 1))
          else if op == 1 then (xs.foldl (· + ·) 0, [])
          else (0, xs.reverse)

def makeTree : Nat → Nat → HeapProbe.Tree
  | 0, start => .leaf start
  | depth+1, start => .branch (makeTree depth start) (makeTree depth (start + 2^depth))
@[noinline] def treeInputIO (depth : Nat) : IO HeapProbe.Tree := pure (makeTree depth 0)
@[noinline] def mirrorIO (tree : HeapProbe.Tree) : IO HeapProbe.Tree := pure (HeapProbe.mirror tree)
def firstLeaf : HeapProbe.Tree → Nat
  | .leaf value => value
  | .branch left _ => firstLeaf left

-- Both input construction and kernel execution cross IO call boundaries.
-- Pure source lets alone do not prevent motion across the clock reads.
def sample (workload : String) (n : Nat) (shared : Bool) : IO (Nat × Nat) := do
  if workload == "mirror" then
    let input ← treeInputIO n
    if shared then
      let keeper ← IO.mkRef input
      let input ← keeper.get
      let before ← IO.monoNanosNow
      let result ← mirrorIO input
      let after ← IO.monoNanosNow
      let original ← keeper.get
      if firstLeaf original != 0 then throw (IO.userError "shared tree changed")
      return (after - before, firstLeaf result)
    else
      let before ← IO.monoNanosNow
      let result ← mirrorIO input
      let after ← IO.monoNanosNow
      return (after - before, firstLeaf result)
  else
    let op := if workload == "map" then 0 else if workload == "fold" then 1 else 2
    let input ← listInputIO n
    if shared then
      let keeper ← IO.mkRef input
      let input ← keeper.get
      let before ← IO.monoNanosNow
      let result ← listKernelIO op input
      let after ← IO.monoNanosNow
      let original ← keeper.get
      if original.headD 0 != 0 then throw (IO.userError "shared list changed")
      return (after - before, if op == 1 then result.1 else result.2.headD 0)
    else
      let before ← IO.monoNanosNow
      let result ← listKernelIO op input
      let after ← IO.monoNanosNow
      return (after - before, if op == 1 then result.1 else result.2.headD 0)

def main (args : List String) : IO Unit := do
  let workload := args[0]!
  let n := args[1]!.toNat!
  let shared := args[2]! == "shared"
  let warmup := args[3]!.toNat!
  let count := args[4]!.toNat!
  for _ in [:warmup] do
    let _ ← sample workload n shared
  for _ in [:count] do
    let (elapsed, result) ← sample workload n shared
    IO.println s!"{elapsed} {result}"
