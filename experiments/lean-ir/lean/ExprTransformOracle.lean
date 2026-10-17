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
private unsafe def emit (label op : String) (input : Expr) (subst : Array Expr) (params : Array Nat) (result : Expr) : IO Unit :=
  let encoding : StateM (Std.HashMap USize Nat) (Json × Array Json × Json) := do
    let inputJson ← encoded input
    let substJson ← subst.mapM encoded
    let outputJson ← encoded result
    pure (inputJson, substJson, outputJson)
  let (inputJson, substJson, outputJson) := encoding.run' {}
  IO.println <| (Json.mkObj [("label", toJson label), ("symbol", toJson op), ("input", inputJson),
    ("substitutions", toJson substJson), ("params", toJson (params.map toString)),
    ("sameRoot", toJson (ptrEq input result)), ("output", outputJson)]).compress
unsafe def main : IO Unit := do
  let t := mkSort .zero
  let f := mkFVar ⟨`x⟩; let g := mkFVar ⟨`y⟩; let metavar := mkMVar ⟨`x⟩
  let subst := #[f, g, f, metavar]
  let cases := #[f, g, metavar, mkBVar 0, mkApp f g, mkLambda `z .implicit f (mkApp f (mkBVar 0)),
    mkForall `q .instImplicit t (mkApp metavar f), mkLet `l f g (mkApp f (mkBVar 0)) true,
    mkMData {} (mkProj `Prod 1 (mkApp f metavar)), mkApp (mkLambda `z .default t f) f]
  for h in [:cases.size] do
    for n in #[0, 1, 2, 4, 9, 18446744073709551621] do
      let e := cases[h]!
      emit s!"abstract-{h}-{n}" "lean_expr_abstract_range" e subst #[n] (e.abstractRange n subst)
  let openTerms := #[mkBVar 0, mkBVar 1, mkBVar 4, mkApp (mkBVar 1) (mkBVar 0),
    mkLambda `z .strictImplicit (mkBVar 0) (mkApp (mkBVar 1) (mkBVar 0)),
    mkForall `z .implicit t (mkBVar 2), mkLet `z t (mkBVar 0) (mkBVar 2) true,
    mkMData {} (mkProj `Prod 0 (mkBVar 0)), t]
  let replacements := #[mkBVar 0, f, mkApp f (mkBVar 1)]
  for h in [:openTerms.size] do
    let e := openTerms[h]!
    emit s!"instantiate1-{h}" "lean_expr_instantiate1" e #[replacements[2]!] #[] (e.instantiate1 replacements[2]!)
    for rev in #[false, true] do
      emit s!"instantiate-{rev}-{h}" (if rev then "lean_expr_instantiate_rev" else "lean_expr_instantiate") e replacements #[]
        (if rev then e.instantiateRev replacements else e.instantiate replacements)
      for (b, en) in #[(0,0), (0,2), (1,3)] do
        emit s!"range-{rev}-{h}-{b}-{en}" (if rev then "lean_expr_instantiate_rev_range" else "lean_expr_instantiate_range") e replacements #[b,en]
          (if rev then e.instantiateRevRange b en replacements else e.instantiateRange b en replacements)
    for (s,d) in #[(0,0), (0,2), (1,1), (4294967296,1), (0,4294967296), (18446744073709551621,1)] do
      emit s!"lift-{h}-{s}-{d}" "lean_expr_lift_loose_bvars" e #[] #[s,d] (e.liftLooseBVars s d)
