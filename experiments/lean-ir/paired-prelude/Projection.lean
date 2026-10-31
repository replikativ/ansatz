import Export

open Lean

namespace MatchedPreludeProducer

def typedName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", typedName p, toJson s]
  | .num p n => Json.arr #[toJson "num", typedName p, toJson (toString n)]

/-- Complete logical checking shape, using the SAME exporter DAG indices.
MData and let.nonDep follow the upstream exporter's documented normalization.
No theorem body is synthesized or omitted. -/
def checkingShape (ci : ConstantInfo) : M Json := do
  let base := [("name", toJson (← dumpName ci.name)),
    ("levelParams", ← dumpUparams ci.levelParams), ("type", toJson (← dumpExpr ci.type))]
  let (kind, extra) ← match ci with
    | .axiomInfo v => pure ("axiom", [("isUnsafe", toJson v.isUnsafe)])
    | .defnInfo v => pure ("def", [("value", toJson (← dumpExpr v.value)),
        ("hints", v.hints.toJson), ("safety", v.safety.toJson), ("all", ← dumpNames v.all)])
    | .thmInfo v => pure ("thm", [("value", toJson (← dumpExpr v.value)), ("all", ← dumpNames v.all)])
    | .opaqueInfo v => pure ("opaque", [("value", toJson (← dumpExpr v.value)),
        ("all", ← dumpNames v.all), ("isUnsafe", toJson v.isUnsafe)])
    | .quotInfo v => pure ("quot", [("kind", v.kind.toJson)])
    | .inductInfo v => pure ("inductive", [("numParams", toJson v.numParams),
        ("numIndices", toJson v.numIndices), ("all", ← dumpNames v.all),
        ("ctors", ← dumpNames v.ctors), ("numNested", toJson v.numNested),
        ("isRec", toJson v.isRec), ("isReflexive", toJson v.isReflexive), ("isUnsafe", toJson v.isUnsafe)])
    | .ctorInfo v => pure ("ctor", [("induct", toJson (← dumpName v.induct)),
        ("cidx", toJson v.cidx), ("numParams", toJson v.numParams),
        ("numFields", toJson v.numFields), ("isUnsafe", toJson v.isUnsafe)])
    | .recInfo v =>
      let rules ← v.rules.mapM fun r => do
        pure <| Json.mkObj [("ctor", toJson (← dumpName r.ctor)),
          ("nfields", toJson r.nfields), ("rhs", toJson (← dumpExpr r.rhs))]
      pure ("rec", [("all", ← dumpNames v.all), ("numParams", toJson v.numParams),
        ("numIndices", toJson v.numIndices), ("numMotives", toJson v.numMotives),
        ("numMinors", toJson v.numMinors), ("rules", toJson rules),
        ("k", toJson v.k), ("isUnsafe", toJson v.isUnsafe)])
  return Json.mkObj [("kind", toJson kind), ("payload", Json.mkObj (base ++ extra))]

/-- Source inventory validation precedes recursive export. All constants, including
unsafe compiler markers and private/internal names, are selected. -/
def auditSource (data : ModuleData) : IO Unit := do
  unless data.constNames.size == data.constants.size && data.constants.size == 2314 do
    throw <| IO.userError "expected complete pinned private Prelude inventory (2314)"
  let mut names : Std.HashMap Name ConstantInfo := {}
  let mut display : Std.HashMap String Name := {}
  for n in data.constNames, ci in data.constants do
    unless n == ci.name && !names.contains n do
      throw <| IO.userError s!"duplicate or mismatched typed name {n}"
    if let some other := display[n.toString]? then
      throw <| IO.userError s!"display-key collision: {repr n} and {repr other}"
    names := names.insert n ci
    display := display.insert n.toString n
  for ci in data.constants do
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? true then deps := deps ++ value.getUsedConstants
    let mut family : List Name := []
    match ci with
    | .defnInfo v => family := v.all
    | .thmInfo v => family := v.all
    | .opaqueInfo v => family := v.all
    | .inductInfo v =>
      family := v.all ++ v.ctors
      for ctor in v.ctors do
        unless (names[ctor]?).any (fun c => match c with
          | .ctorInfo c => c.induct == v.name
          | _ => false) do
          throw <| IO.userError s!"incomplete constructor family {v.name}"
    | .ctorInfo v =>
      family := [v.induct]
      unless (names[v.induct]?).any (fun c => match c with
        | .inductInfo i => i.ctors.contains v.name
        | _ => false) do
        throw <| IO.userError s!"orphan constructor {v.name}"
    | .recInfo v =>
      family := v.all ++ v.rules.map (·.ctor)
      for r in v.rules do deps := deps ++ r.rhs.getUsedConstants
    | _ => pure ()
    for n in deps do
      unless names.contains n do throw <| IO.userError s!"unresolved dependency {ci.name} -> {n}"
    for n in family do
      unless names.contains n do throw <| IO.userError s!"missing family member {ci.name} -> {n}"
  for n in [`Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
    unless (names[n]?).any (fun c => match c with | .quotInfo _ => true | _ => false) do
      throw <| IO.userError s!"missing genuine quotient declaration {n}"

end MatchedPreludeProducer
