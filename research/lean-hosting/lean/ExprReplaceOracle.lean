import Lean
open Lean
private unsafe def callback (labels : Array (Expr × String)) (log : IO.Ref (Array String))
    (wanted : Option Expr) (replacement : Expr) (e : Expr) : Option Expr := unsafeBaseIO do
  log.modify (·.push ((labels.find? (fun x => ptrEq x.1 e)).map Prod.snd |>.getD "unknown"))
  return if wanted.any (ptrEq e) then some replacement else none
unsafe def main : IO Unit := do
  let b := mkBVar 0; let replacement := mkBVar 1
  let a := mkApp b b; let root := mkApp a a
  let labels := #[(root,"root"),(a,"app"),(b,"bound")]
  for (name,wanted) in #[("none",none),("root",some root),("app",some a),("bound",some b)] do
    let log ← IO.mkRef #[]
    let out ← IO.mkRef root
    out.set (root.replace (callback labels log wanted replacement))
    let result ← out.get
    IO.println <| (Json.mkObj [("case",toJson name),("visits",toJson (← log.get)),
      ("unchanged",toJson (ptrEq root result)),("data",toJson (toString result.data.toNat))]).compress
