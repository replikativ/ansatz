import Lean

/- Runtime argv inputs keep the opaque native calls dependent on observed input.
   Only valid Bool/Nat range domains are invoked: native panic is not tested. -/
def value (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw <| IO.userError "expected decimal Nat"

def main (args : List String) : IO Unit := do
  for input in args do
    let parts := input.splitOn ":"
    match parts with
    | ["expr", h, r, d, a, b, c, e] =>
      let h ← value h; let r ← value r; let d ← value d
      let a ← value a; let b ← value b; let c ← value c; let e ← value e
      IO.println (Lean.Expr.mkData h.toUInt64 r d.toUInt32 (a == 1) (b == 1) (c == 1) (e == 1)).toNat
    | ["level", h, d, a, b] =>
      let h ← value h; let d ← value d; let a ← value a; let b ← value b
      IO.println (Lean.Level.mkData h.toUInt64 d (a == 1) (b == 1)).toNat
    | ["app", f, a] =>
      let f ← value f; let a ← value a
      IO.println (Lean.Expr.mkAppData f.toUInt64 a.toUInt64).toNat
    | _ => throw <| IO.userError "bad vector"
