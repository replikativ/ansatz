import Lean.Elab.Command
import Lean.AddDecl
import RawCasesOnOracle

open Lean Elab Command

namespace RawCasesOnPayloadSupport

private def fullDefinitionEqual (left right : Declaration) : Bool :=
  match left, right with
  | .defnDecl left, .defnDecl right =>
    left.name == right.name && left.levelParams == right.levelParams &&
    left.type.equal right.type && left.value.equal right.value &&
    left.hints == right.hints && left.safety == right.safety && left.all == right.all
  | _, _ => false

private def hasMarker (expression : Expr) : Bool :=
  (expression.find? fun expression =>
    match expression with
    | .mdata metadata _ => metadata.getString `oracle.marker == "preserve-this-payload" &&
      match metadata.find `oracle.syntax with
      | some (.ofSyntax (.node .none `oracle.payload #[.atom .none "opaque"])) => true
      | _ => false
    | _ => false).isSome

private def hasLet (expression : Expr) (flag : Bool) : Bool :=
  (expression.find? fun expression =>
    match expression with
    | .letE _ _ _ _ nondep => nondep == flag
    | _ => false).isSome

private def markedIndex (expression : Expr) (index : Nat) : Bool :=
  (expression.find? fun expression =>
    match expression with
    | .mdata metadata body => metadata.getString `oracle.marker == "preserve-this-payload" &&
      (body.find? fun expression => match expression with | .bvar actual => actual == index | _ => false).isSome
    | _ => false).isSome

private def requireCoverage (input : Kernel.Environment) (name : Name)
    (kind : RawCasesOnOracle.AnnotatedField) (output : Declaration) : CoreM Unit := do
  let some (.recInfo recursor) := input.find? (Name.str name "rec")
    | throwError "Expected admitted raw recursor"
  let .defnDecl output := output | throwError "Expected casesOn definition"
  unless hasMarker recursor.type && hasMarker output.type &&
      markedIndex recursor.type 1 && markedIndex output.type 2 do
    throwError "Missing marker/Syntax or actual changed-descendant coverage"
  match kind with
  | .dependentLet => unless hasLet recursor.type false && hasLet output.type false do
      throwError "Dependent let annotation was lost"
  | .nondependentLet => unless hasLet recursor.type true && hasLet output.type true do
      throwError "Nondependent let annotation was lost"
  | .metadata => pure ()

elab "checked_cases_payload" : command => do
  liftCoreM do
    if (← getEnv).header.isModule then throwError "Classic fixture module required"
    if debug.skipKernelTC.get (← getOptions) then throwError "Kernel checking must remain enabled"
    for (suffix, kind, imax) in [
        ("Metadata", RawCasesOnOracle.AnnotatedField.metadata, false),
        ("DependentLet", RawCasesOnOracle.AnnotatedField.dependentLet, false),
        ("NondependentLet", RawCasesOnOracle.AnnotatedField.nondependentLet, false),
        ("IMax", RawCasesOnOracle.AnnotatedField.metadata, true)] do
      let name := Name.str `RawCasesOnPayload suffix
      if (← getEnv).contains name then throwError "Fixture input name already exists"
      addDecl (RawCasesOnOracle.annotatedDeclaration name kind imax) (forceExpose := true)
      let input := (← getEnv).toKernelEnv
      if (input.find? (Name.str name "casesOn")).isSome then
        throwError "Native answer must be absent before construction"
      let native ← ofExceptKernelException (mkCasesOnImp input name)
      let port ← ofExceptKernelException (KernelCasesOnRaw.construct input name)
      unless fullDefinitionEqual native port do throwError "Native/port full definition mismatch"
      requireCoverage input name kind native
      let _ ← ofExceptKernelException <| input.addDeclCore 0 0 port none
      addDecl native (forceExpose := true)

end RawCasesOnPayloadSupport
