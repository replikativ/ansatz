import Lean.Compiler.IR.Checker

-- Explicit runtime arguments prevent precomputed boundary-vector results.
-- Four U32 values followed by four U64 values; see README for the pinned command.
def main (args : List String) : IO Unit := do
  unless args.length == 8 do
    throw (IO.userError "expected four U32 values followed by four U64 values")
  let mut ns : Array Nat := #[]
  for text in args do
    let some n := text.toNat? | throw (IO.userError "invalid natural input")
    ns := ns.push n
  IO.println s!"layout={Lean.IR.Checker.getMaxCtorFields ()},{Lean.IR.Checker.getMaxCtorScalarsSize ()},{Lean.IR.Checker.getMaxCtorTag ()},{Lean.IR.Checker.getUSizeSize ()}"
  for i in [:4] do
    for j in [:4] do
      let a := UInt32.ofNat ns[i]!
      let b := UInt32.ofNat ns[j]!
      IO.println s!"u32:{a.toNat}:{b.toNat}={if a < b then 1 else 0}"
  for i in [4:8] do
    let a := UInt64.ofNat ns[i]!
    IO.println s!"u64:{ns[i]!}={a.toNat}"
