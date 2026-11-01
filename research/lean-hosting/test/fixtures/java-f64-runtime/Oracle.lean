@[extern "ansatz_f64_nearest"] opaque nearest (u : Unit) : UInt8
@[extern "ansatz_f64_c_locale"] opaque cLocale (u : Unit) : UInt8
@[extern "ansatz_f64_canonical_nan"] opaque canonicalNaN (u : Unit) : UInt8
def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn s!"profile|{nearest ()}|{cLocale ()}|{canonicalNaN ()}"
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let parts := line.trimAscii.toString.splitOn " "
    let op := parts[0]!
    let a := (parts[1]!).toNat!
    let b := (parts[2]!).toNat!
    let x := Float.ofBits a.toUInt64
    let y := Float.ofBits b.toUInt64
    let z := if op == "u64" then a.toUInt64.toFloat
             else if op == "nat" then Float.ofNat a
             else if op == "sub" then x - y
             else if op == "mul" then x * y
             else if op == "div" then x / y
             else x
    let comparison := if op == "eq" then (if x == y then 1 else 0)
                      else if op == "lt" then (if x < y then 1 else 0)
                      else 2
    output.putStrLn s!"{z.toBits.toNat}|{z.toString}|{comparison}"
