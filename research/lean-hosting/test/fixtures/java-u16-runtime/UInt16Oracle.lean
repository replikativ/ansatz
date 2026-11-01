import Init

-- Runtime inputs: 0 255 256 32767 32768 65535.
def main (args : List String) : IO Unit := do
  unless args.length == 6 do
    throw (IO.userError "expected six canonical UInt16 decimal values")
  let mut xs : Array UInt16 := #[]
  for text in args do
    let some n := text.toNat? | throw (IO.userError "invalid Nat")
    unless n <= 65535 do throw (IO.userError "noncanonical UInt16")
    xs := xs.push (UInt16.ofNat n)
  for a in xs do
    IO.println s!"nat:{a.toNat}"
    for b in xs do
      IO.println s!"eq:{a.toNat}:{b.toNat}={if a == b then 1 else 0}"
