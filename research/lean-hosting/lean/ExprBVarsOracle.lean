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
private unsafe def emitLower (label : String) (e : Expr) (s d : Nat) : IO Unit := do
  let result := e.lowerLooseBVars s d
  let encoding : StateM (Std.HashMap USize Nat) Json := do
    let input ← encoded e
    let output ← encoded result
    pure <| Json.mkObj [("label",toJson label),("symbol",toJson "lean_expr_lower_loose_bvars"),
      ("input",input),("params",toJson #[toString s,toString d]),("sameRoot",toJson (ptrEq e result)),("output",output)]
  IO.println (encoding.run' {}).compress
private unsafe def emitHas (label : String) (e : Expr) (i : Nat) : IO Unit := do
  IO.println <| (Json.mkObj [("label",toJson label),("symbol",toJson "lean_expr_has_loose_bvar"),
    ("input",(encoded e).run' {}),("params",toJson #[toString i]),("result",toJson (e.hasLooseBVar i))]).compress
unsafe def main : IO Unit := do
  let b := mkBVar 0; let c := mkBVar 1; let d := mkBVar 3; let t := mkSort .zero
  let a := mkApp c d
  let cases := #[b,c,d,t,mkApp a a,mkLambda `l .strictImplicit c a,
    mkForall `p .instImplicit t (mkApp b c),mkLet `v t a (mkApp c d) true,
    mkMData {} (mkProj `Prod 0 a),mkLambda `outer .default t (mkLambda `inner .implicit t d)]
  for j in [:cases.size] do
    let e := cases[j]!
    for i in #[0,1,2,3,4,4294967296,4294967297,9223372036854775808] do
      emitHas s!"has-{j}-{i}" e i
    for (s,d) in #[(0,0),(1,1),(2,1),(3,2),(0,1),(4294967296,0),(4294967296,1),
                   (4294967297,1),(1,4294967296),(9223372036854775808,1),(1,9223372036854775808)] do
      emitLower s!"lower-{j}-{s}-{d}" e s d
