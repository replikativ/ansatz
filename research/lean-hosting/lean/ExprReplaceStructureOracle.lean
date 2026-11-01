import Lean
open Lean
private def named (n : Name) : Json :=
  match n with
  | .anonymous => Json.mkObj [("kind", toJson "name"), ("tag", toJson 0)]
  | .str p s => Json.mkObj [("kind", toJson "name"), ("tag", toJson 1), ("parent", named p), ("value", toJson s), ("hash", toJson (toString (hash n)))]
  | .num p n => Json.mkObj [("kind", toJson "name"), ("tag", toJson 2), ("parent", named p), ("value", toJson (toString n)), ("hash", toJson (toString (hash (Name.num p n))))]
private def bi : BinderInfo → Nat | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
private unsafe def encoded (e : Expr) : StateM (Std.HashMap USize Nat) Json := do
  let address := ptrAddrUnsafe e
  let ids ← get
  let id ← match ids[address]? with
    | some id => pure id
    | none => do
      let id := ids.size
      set (ids.insert address id)
      pure id
  let (tag, fields, annotation) : Nat × Array Json × Option Nat ← match e with
    | .bvar i => do pure (0, #[toJson (toString i)], none)
    | .fvar n => do pure (1, #[named n.name], none)
    | .mvar n => do pure (2, #[named n.name], none)
    | .sort .zero => do pure (3, #[toJson 0], none)
    | .const n [] => do pure (4, #[named n, toJson 0], none)
    | .app f a => do pure (5, #[(← encoded f), (← encoded a)], none)
    | .lam n t b info => do pure (6, #[named n, (← encoded t), (← encoded b)], some (bi info))
    | .forallE n t b info => do pure (7, #[named n, (← encoded t), (← encoded b)], some (bi info))
    | .letE n t v b nd => do pure (8, #[named n, (← encoded t), (← encoded v), (← encoded b)], some (if nd then 1 else 0))
    | .mdata _ b => do pure (10, #[toJson "empty-metadata", (← encoded b)], none)
    | .proj n i b => do pure (11, #[named n, toJson (toString i), (← encoded b)], none)
    | _ => pure <| panic! "unsupported oracle expression"
  return Json.mkObj [("kind", toJson "expr"), ("tag", toJson tag), ("fields", toJson fields),
    ("data", toJson (toString e.data.toNat)), ("annotation", toJson annotation), ("nodeId", toJson id)]
private unsafe def callback (log : IO.Ref (Array Expr)) (target replacement : Expr) (e : Expr) : Option Expr := unsafeBaseIO do
  log.modify (·.push e)
  return if ptrEq target e then some replacement else none
private unsafe def emit (label : String) (input target replacement : Expr) : IO Unit := do
  let log ← IO.mkRef #[]
  let output ← IO.mkRef input
  output.set (input.replace (callback log target replacement))
  let result ← output.get
  let visits ← log.get
  let encoding : StateM (Std.HashMap USize Nat) Json := do
    let inputJson ← encoded input
    let targetJson ← encoded target
    let replacementJson ← encoded replacement
    let outputJson ← encoded result
    let visitsJson ← visits.mapM encoded
    pure <| Json.mkObj [("label",toJson label),("input",inputJson),("target",targetJson),
      ("replacement",replacementJson),("output",outputJson),("visits",toJson visitsJson),
      ("sameRoot",toJson (ptrEq input result))]
  IO.println (encoding.run' {}).compress
unsafe def main : IO Unit := do
  let b := mkBVar 0; let c := mkBVar 1; let t := mkSort .zero
  let a := mkApp b c
  emit "lambda-existing-descendant" (mkLambda `lambda .strictImplicit b a) b c
  emit "forall-fresh-app" (mkForall `forallName .instImplicit t a) a (mkApp c c)
  let body := mkApp c b
  emit "let-existing-body" (mkLet `localName t a body true) b body
  emit "metadata-existing-descendant" (mkMData {} (mkProj `Prod 1 a)) b c
  emit "projection-grandchild" (mkProj `Prod 0 a) a b
  let same := mkLambda `same .implicit t a
  emit "some-original-root" same same same
  let closed := mkLambda `closed .strictImplicit t b
  emit "closed-layout" closed closed closed
