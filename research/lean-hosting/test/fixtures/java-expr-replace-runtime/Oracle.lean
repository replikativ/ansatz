import Lean

/- Only unambiguous source Expr values. No numeric pointer addresses or JVM
   host-counter claims. Arbitrary effectful callback traces are separate tests. -/
unsafe def main : IO Unit := do
  let r ← IO.mkRef (7 : Nat)
  let n ← r.get
  let a := Lean.Expr.bvar n
  let root := Lean.Expr.app a a
  let unchanged := root.replace fun _ => none
  IO.println s!"none-identity: {ptrEq root unchanged}"
  let self := root.replace fun e => some e
  IO.println s!"some-self: {ptrEq root self}"
  let stopped := root.replace fun _ => some (.bvar 42)
  IO.println s!"some-stop: {stopped == .bvar 42}"
  let changed := root.replace fun e => match e with
    | .bvar i => some (.bvar (i + 1))
    | _ => none
  IO.println s!"changed-content: {changed == .app (.bvar 8) (.bvar 8)}"
  match changed with
  | .app f a => IO.println s!"shared-cache-result: {ptrEq f a}"
  | _ => IO.println "shared-cache-result: false"
