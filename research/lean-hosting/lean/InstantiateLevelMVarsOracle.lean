import Lean
open Lean

private def nm (s : String) : Name := .str .anonymous s
private def mv (s : String) : Level := .mvar ⟨nm s⟩
private def p (s : String) : Level := .param (nm s)
private unsafe def encode (l : Level) : Json :=
  let children := match l with
    | .zero => #[toJson "zero"]
    | .succ x => #[toJson "succ", encode x]
    | .max x y => #[toJson "max", encode x, encode y]
    | .imax x y => #[toJson "imax", encode x, encode y]
    | .param n => #[toJson "param", toJson n.toString]
    | .mvar n => #[toJson "mvar", toJson n.name.toString]
  Json.mkObj [("tree", Json.arr children), ("data", toJson (toString (unsafeCast l.data : UInt64)))]
private unsafe def caseJson (label : String) (assignments : Array (String × Level)) (input : Level) : Json := Id.run do
  let before := assignments.foldl (init := ({} : MetavarContext)) fun m (n,l) => assignLevelMVarExp m ⟨nm n⟩ l
  let (after, result) := instantiateLevelMVarsImp before input
  let finalAssignments := assignments.map fun (n,_) =>
    Json.arr #[toJson n, encode (after.lAssignment.find! ⟨nm n⟩)]
  let shared := match result with
    | .max a (.imax b _) => ptrEq a b
    | _ => false
  return Json.mkObj [("label", toJson label), ("input", encode input),
    ("assignments", toJson (assignments.map fun (n,l) => (n, encode l))),
    ("result", encode result), ("finalAssignments", toJson finalAssignments),
    ("sameContext", toJson (ptrEq before after)), ("sameLevel", toJson (ptrEq input result)),
    ("sharedResultChildren", toJson shared)]

unsafe def main : IO Unit := do
  let shared := Level.succ (mv "x")
  let cases := #[
    caseJson "closed unchanged" #[] (.max (.succ (.param (nm "u"))) .zero),
    caseJson "unassigned" #[] (mv "x"),
    caseJson "direct assignment" #[("x", .zero)] (mv "x"),
    caseJson "nested writeback" #[("x", .succ (mv "y")), ("y", .zero)] (mv "x"),
    caseJson "chain writeback" #[("x", mv "y"), ("y", mv "z"), ("z", .zero)] (mv "x"),
    caseJson "max zero" #[("x", .zero)] (.max (mv "x") .zero),
    caseJson "imax zero" #[("x", .zero)] (.imax (p "u") (mv "x")),
    caseJson "imax one" #[("x", mv "y")] (.imax (.succ .zero) (mv "x")),
    caseJson "max offsets" #[("x", p "u")] (.max (.succ (mv "x")) (.succ (.succ (mv "x")))),
    caseJson "max subsumption" #[("x", p "v")] (.max (mv "x") (.max (mv "x") (p "u"))),
    caseJson "shared cache" #[("x", p "u")] (.max shared (.imax shared (mv "y"))),
    caseJson "unresolved assignment unchanged" #[("x", .succ (mv "y"))] (mv "x")]
  for c in cases do IO.println c.compress
