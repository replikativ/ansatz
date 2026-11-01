-- Differential oracle for the explicit 64-bit JVM runtime profile.
def main (args : List String) : IO Unit := do
  for input in args do
    match input.splitOn "," with
    | ["usize", a] =>
      let value := a.toNat!.toUSize
      IO.println ("usize," ++ a ++ "," ++ toString value.toNat ++ "," ++ USize.repr value)
    | ["u32", a, b] =>
      let x := a.toNat!.toUInt32
      let y := b.toNat!.toUInt32
      IO.println ("u32," ++ a ++ "," ++ b ++ "," ++ toString x.toNat ++ "," ++
        toString y.toNat ++ "," ++ (if x = y then "1" else "0") ++ "," ++
        (if x ≤ y then "1" else "0"))
    | _ => throw (IO.userError "expected usize,nat or u32,nat,nat")
