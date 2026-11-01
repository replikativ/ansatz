import Lean
open Lean

private def nm (s : String) : Name := .str .anonymous s
private def mv (s : String) : Expr := mkMVar ⟨nm s⟩
private def fv (s : String) : Expr := mkFVar ⟨nm s⟩
private def c (s : String) : Expr := mkConst (nm s)
private def ty : Expr := mkSort .zero
private def ne (n : Name) : Json := Json.mkObj [("name", toJson n.toString), ("hash", toJson (toString (hash n)))]
private unsafe def le (l : Level) : Json :=
  let tree := match l with
    | .zero => #[toJson "zero"]
    | .succ a => #[toJson "succ", le a]
    | .max a b => #[toJson "max", le a, le b]
    | .imax a b => #[toJson "imax", le a, le b]
    | .param n => #[toJson "param", ne n]
    | .mvar n => #[toJson "mvar", ne n.name]
  Json.mkObj [("id", toJson (toString (ptrAddrUnsafe l))), ("tree", toJson tree), ("data", toJson (toString (unsafeCast l.data : UInt64)))]
private def bi : BinderInfo → Nat
  | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3
private unsafe def ee (e : Expr) : Json :=
  let tree := match e with
    | .bvar n => #[toJson "bvar", toJson (toString n)]
    | .fvar n => #[toJson "fvar", ne n.name]
    | .mvar n => #[toJson "mvar", ne n.name]
    | .sort l => #[toJson "sort", le l]
    | .const n ls => #[toJson "const", ne n, toJson (ls.map le)]
    | .app f a => #[toJson "app", ee f, ee a]
    | .lam n d b info => #[toJson "lam", ne n, ee d, ee b, toJson (bi info)]
    | .forallE n d b info => #[toJson "forall", ne n, ee d, ee b, toJson (bi info)]
    | .letE n t v b nondep => #[toJson "let", ne n, ee t, ee v, ee b, toJson nondep]
    | .lit (.natVal n) => #[toJson "nat", toJson (toString n)]
    | .lit (.strVal s) => #[toJson "string", toJson s]
    | .mdata _ e => #[toJson "mdata", ee e]
    | .proj n i e => #[toJson "proj", ne n, toJson (toString i), ee e]
  Json.mkObj [("id", toJson (toString (ptrAddrUnsafe e))), ("tree", toJson tree), ("data", toJson (toString (unsafeCast e.data : UInt64)))]

private unsafe def oracle (label : String) (es : Array (String × Expr))
    (ds : Array (String × Array Expr × String)) (input : Expr)
    (ls : Array (String × Level) := #[]) : Json := Id.run do
  let before := es.foldl (init := ({} : MetavarContext)) fun m (n,e) => assignExp m ⟨nm n⟩ e
  let before := ds.foldl (init := before) fun m (n, fvars, pending) =>
    {m with dAssignment := m.dAssignment.insert ⟨nm n⟩ {fvars, mvarIdPending := ⟨nm pending⟩}}
  let before := ls.foldl (init := before) fun m (n,l) => assignLevelMVarExp m ⟨nm n⟩ l
  let (after, output) := instantiateExprMVarsImp before input
  let appShared := match output with | .app a b => ptrEq a b | _ => false
  let prefixShared := match input, output with | .app f _, .app g _ => ptrEq f g | _, _ => false
  let ctxEs := es.map fun (n,_) => (n, ee (after.eAssignment.find! ⟨nm n⟩))
  let ctxLs := ls.map fun (n,_) => (n, le (after.lAssignment.find! ⟨nm n⟩))
  let names := (es.map fun (n,_) => ne (nm n)) ++ (ls.map fun (n,_) => ne (nm n)) ++
    (ds.flatMap fun (n,_,p) => #[ne (nm n), ne (nm p)])
  return Json.mkObj [("names", toJson names), ("label", toJson label), ("input", ee input), ("result", ee output),
    ("assignments", toJson (es.map fun (n,e) => (n, ee e))),
    ("levelAssignments", toJson (ls.map fun (n,l) => (n, le l))),
    ("delayed", toJson (ds.map fun (n,xs,p) => (n, xs.map ee, p))),
    ("finalAssignments", toJson ctxEs), ("finalLevelAssignments", toJson ctxLs),
    ("sameContext", toJson (ptrEq before after)), ("sameExpr", toJson (ptrEq input output)),
    ("appShared", toJson appShared), ("prefixShared", toJson prefixShared)]

unsafe def main : IO Unit := do
  let x := fv "x"
  let y := fv "y"
  let shared := mkApp (mv "m") (c "A")
  let appPrefix := mkApp (c "F") (c "A")
  let cases := #[
    oracle "closed unchanged" #[] #[] (mkApp (c "F") (c "A")),
    oracle "unassigned" #[] #[] (mv "m"),
    oracle "direct" #[("m", c "A")] #[] (mv "m"),
    oracle "chain writeback" #[("m", mv "n"), ("n", mv "p"), ("p", c "A")] #[] (mv "m"),
    oracle "unresolved assignment" #[("m", mkApp (c "F") (mv "n"))] #[] (mv "m"),
    oracle "beta" #[("m", mkLambda (nm "a") .default ty (mkBVar 0))] #[] (mkApp (mv "m") (c "A")),
    oracle "beta extra" #[("m", mkLambda (nm "a") .default ty (mkBVar 0))] #[] (mkApp2 (mv "m") (c "F") (c "A")),
    oracle "zeta beta" #[("m", mkLet (nm "a") ty (c "A") (mkLambda (nm "b") .default ty (mkBVar 1)))] #[] (mkApp (mv "m") (c "B")),
    oracle "prefix sharing" #[("m", c "B")] #[] (mkApp appPrefix (mv "m")),
    oracle "shared cache" #[("m", c "F")] #[] (mkApp shared shared),
    oracle "binders metadata proj let" #[("m", c "A")] #[]
      (mkLet (nm "z") (mv "m") (mkMData {} (mv "m"))
        (mkForall (nm "a") .implicit (mv "m") (mkLambda (nm "b") .instImplicit ty (mkProj (nm "P") 3 (mv "m")))) true),
    oracle "level sorts" #[] #[] (mkApp (mkSort (.mvar ⟨nm "u"⟩)) (mkConst (nm "T") [.mvar ⟨nm "u"⟩])) #[("u", .succ .zero)],
    oracle "delayed simple" #[("p", x)] #[("d", #[x], "p")] (mkApp (mv "d") (c "A")),
    oracle "delayed extra beta" #[("p", mkLambda (nm "y") .default ty x)] #[("d", #[x], "p")]
      (mkApp2 (mv "d") (c "A") (c "B")),
    oracle "delayed binder lift" #[("p", mkLambda (nm "y") .default ty x)] #[("d", #[x], "p")]
      (mkApp (mv "d") (mkBVar 0)),
    oracle "delayed reentered scopes" #[("p", mkApp (c "F") x)] #[("d", #[x], "p")]
      (mkApp2 (c "Pair") (mkApp (mv "d") (c "A")) (mkApp (mv "d") (c "B"))),
    oracle "delayed shadowed fvar" #[("p", mkApp (mv "e") x), ("q", x)]
      #[("d", #[x], "p"), ("e", #[x], "q")] (mkApp (mv "d") (c "A")),
    oracle "delayed unresolved cut writeback" #[("p", mkApp2 (c "Pair") (mkApp (mv "e") (c "A")) (mv "unknown")), ("q", y)]
      #[("d", #[x], "p"), ("e", #[y], "q")] (mkApp (mv "d") (c "B")),
    oracle "delayed bare zero args" #[("p", c "A")] #[("d", #[], "p")] (mv "d"),
    oracle "delayed too few args" #[("p", x)] #[("d", #[x,y], "p")] (mkApp (mv "d") (c "A")),
    oracle "delayed pending unassigned" #[] #[("d", #[x], "p")] (mkApp (mv "d") (c "A")),
    oracle "direct precedence" #[("d", c "F"), ("p", x)] #[("d", #[x], "p")] (mkApp (mv "d") (c "A"))]
  for c in cases do IO.println c.compress
