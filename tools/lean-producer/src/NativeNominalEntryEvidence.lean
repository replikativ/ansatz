import NativeTypeGraph

/-!
Private checkpoint facade for future v3 entry evidence. These functions inspect
closed type roots only. They do not accept selected-entry requests, certify a
callable, issue source/cache/artifact evidence, or register a producer cohort.
The immutable v1/v2 helpers remain independent of this module.
-/
open Lean

namespace NativeNominalEntryEvidence

/-- Advisory complete origin inventory. No product claims/admitted graph. -/
def inventoryTypes (roots : Array Expr) : MetaM Json :=
  NativeTypeGraph.inventoryOrigins roots

private def encode (e : Expr) : MetaM Json :=
  match NativeEntryTransport.encodeType e with
  | .ok value => pure value
  | .error reason => throwError "NominalObservation: {reason}"

/-- Observe actual closed types and each logical field's lowering separately
    from generic declaration storage. The supplied products must come from a
    real captured manifest; this function alone does not authenticate it. -/
def observeTypes (roots : Array Expr) (products : NativeTypeGraph.ModuleProducts) : MetaM Json := do
  let result ← NativeTypeGraph.discover roots products
  let mut checks := #[]
  for index in [:result.canonicalRoots.size] do
    let expected := result.canonicalRoots[index]!
    let mut actual? := none
    for root in roots do
      if ← Meta.withTransparency .default (Meta.isDefEq root expected) then
        actual? := some root
        break
    let some actual := actual? | throwError "NominalObservation: missing canonical root native DefEq"
    checks := checks.push <| Json.mkObj [("root", toJson index),
      ("algorithm", toJson "Lean.Meta.isDefEq"), ("transparency", toJson "default"),
      ("actualType", ← encode actual), ("expectedType", ← encode expected)]
  let document := Json.mkObj [("schema", toJson "lean-jvm-private-nominal-observations/1"),
    ("scope", toJson "private-no-cohort-admission"),
    ("typeGraph", result.logical), ("rootTypeChecks", Json.arr checks),
    ("representation", result.layouts)]
  unless document.compress.utf8ByteSize ≤ 4194304 do
    throwError "NominalObservation: encoded observation byte budget"
  return document

end NativeNominalEntryEvidence
