-- Native oracle for the JVM research runtime, pinned to Lean 4.33.1.
-- Inputs arrive at runtime to avoid evaluating literal expressions at compile time.
def main (args : List String) : IO Unit := do
  for input in args do
    match input.splitOn "," with
    | [op, a, b] =>
      let x := a.toNat!
      let y := b.toNat!
      let value ← match op with
        | "mul" => pure (x * y)
        | "div" => pure (x / y)
        | "pow" => pure (x ^ y)
        | _ => throw (IO.userError "unknown operation")
      IO.println (op ++ "," ++ a ++ "," ++ b ++ "," ++ toString value)
    | _ => throw (IO.userError "expected operation,nat,nat")
