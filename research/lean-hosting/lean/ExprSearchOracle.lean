import Lean
open Lean
private unsafe def label (labels : Array (Expr × String)) (e : Expr) : String :=
  (labels.find? (fun pair => ptrEq pair.1 e)).map Prod.snd |>.getD "unknown"
private unsafe def predicate (labels : Array (Expr × String)) (log : IO.Ref (Array String))
    (wanted : Option Expr) (e : Expr) : Bool := unsafeBaseIO do
  log.modify (·.push (label labels e))
  return wanted.any (ptrEq e)
private unsafe def extendedPredicate (labels : Array (Expr × String)) (log : IO.Ref (Array String))
    (wanted prune : Option Expr) (e : Expr) : Expr.FindStep := unsafeBaseIO do
  log.modify (·.push (label labels e))
  return if wanted.any (ptrEq e) then .found else if prune.any (ptrEq e) then .done else .visit
unsafe def main : IO Unit := do
  let b := mkBVar 0; let f := mkFVar ⟨`x⟩; let s := mkSort .zero; let c := mkConst `Nat
  let a := mkApp f b; let shared := mkApp a a
  let l := mkLambda `x .default s shared
  let projection := mkProj `Prod 0 b; let md := mkMData {} projection
  let root := mkLet `x c l md
  let labels := #[(root,"let"), (c,"const"), (l,"lambda"), (s,"sort"), (shared,"shared-app"),
    (a,"app"), (f,"free"), (b,"bound"), (md,"metadata"), (projection,"projection")]
  for (name,wanted) in #[("none",none), ("root",some root), ("free",some f), ("bound",some b)] do
    let log ← IO.mkRef #[]
    let result ← IO.mkRef (none : Option Expr)
    result.set (root.find? (predicate labels log wanted))
    let found ← result.get
    IO.println <| (Json.mkObj [("case",toJson name), ("extended",toJson false), ("visits",toJson (← log.get)),
      ("found",toJson (found.map (label labels)))]).compress
  for (name,wanted,prune) in #[("none",none,none), ("root",some root,none),
      ("free",some f,none), ("bound-prune",some b,some shared)] do
    let log ← IO.mkRef #[]
    let result ← IO.mkRef (none : Option Expr)
    result.set (root.findExt? (extendedPredicate labels log wanted prune))
    let found ← result.get
    IO.println <| (Json.mkObj [("case",toJson name), ("extended",toJson true), ("visits",toJson (← log.get)),
      ("found",toJson (found.map (label labels)))]).compress
