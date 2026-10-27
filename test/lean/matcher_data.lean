import Lean

open Lean Meta Match

-- Reference for the pure Basic and MatcherInfo operations; no matcher compiler claim.
run_meta do
  let x : FVarId := ⟨`x⟩
  let y : FVarId := ⟨`y⟩
  let z : FVarId := ⟨`z⟩
  let s : FVarSubst := ({} : FVarSubst).insert x (mkFVar y)
  let p := Pattern.ctor ``Nat.succ [] [mkFVar x] [.var y]
  match p.applyFVarSubst s with
  | .ctor _ _ [e] [.var v] =>
    unless e == mkFVar y && v == y do throwError "constructor substitution"
  | _ => throwError "constructor pattern shape"
  match (Pattern.var x).applyFVarSubst s with
  | .inaccessible e => unless e == mkFVar y do throwError "variable substitution"
  | _ => throwError "variable should become inaccessible"
  match (Pattern.as x (.var y) z).applyFVarSubst s with
  | .var v => unless v == y do throwError "alias body"
  | _ => throwError "replaced alias should disappear"
  match Example.applyFVarSubst s (.var x) with
  | .var v => unless v == y do throwError "counterexample renaming"
  | _ => throwError "counterexample shape"
  let t : FVarSubst := ({} : FVarSubst).insert x (mkNatLit 0)
  match Example.applyFVarSubst t (.var x) with
  | .underscore => pure ()
  | _ => throwError "nonvariable counterexamples should become underscores"
  let info : MatcherInfo := {
    numParams := 2, numDiscrs := 2,
    altInfos := #[⟨1, 0, false⟩, ⟨0, 1, false⟩],
    uElimPos? := some 0,
    discrInfos := #[⟨some `h⟩, ⟨none⟩],
    overlaps := ({} : Overlaps).insert 0 1
  }
  unless info.arity == 7 && info.getMotivePos == 2 &&
         info.getFirstDiscrPos == 3 && info.getFirstAltPos == 5 &&
         info.getNumDiscrEqs == 1 && info.altNumParams == #[2, 2] do
    throwError "matcher parameter layout"
  let o := ({} : Overlaps).insert 3 2 |>.insert 0 2 |>.insert 3 2 |>.insert 2 3
  unless o.overlapping 2 == #[0, 3] && o.overlapping 3 == #[2] do
    throwError "overlap orientation and ordering"
