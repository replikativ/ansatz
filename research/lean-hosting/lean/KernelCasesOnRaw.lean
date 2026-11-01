/-
Algorithm adapted from Lean src/library/constructions/cases_on.cpp at
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Copyright (c) 2014 Microsoft Corporation. Original author: Leonardo de Moura.
Released under Apache 2.0; see LICENSE.
-/
import Lean.Environment
import Lean.LocalContext
import Lean.Util.FindExpr

namespace KernelCasesOnRaw
open Lean

-- These operations keep actual Expr/Level/Name values, including opaque metadata
-- and letE.nondep. No checking projection or Java reconstruction occurs here.
private partial def piUnit (type unit : Expr) : Expr :=
  match type with
  | .forallE name domain body _ => mkForall name .default domain (piUnit body unit)
  | _ => unit

private partial def funUnit (type unit : Expr) : Expr :=
  match type with
  | .forallE name domain body _ => mkLambda name .default domain (funUnit body unit)
  | _ => unit

/-- C++ operator<< uses escape=false but still prints an empty component as «».
Name.toString's escaping modes differ on empty names, so do not substitute it. -/
private def nativeNameString (name : Name) : String := Id.run do
  let mut current := name
  let mut parts : List String := []
  repeat
    match current with
    | .anonymous => break
    | .str parent part =>
      parts := (if part.isEmpty then "«»" else part) :: parts
      current := parent
    | .num parent part =>
      parts := toString part :: parts
      current := parent
  return if parts.isEmpty then "[anonymous]" else String.intercalate "." parts

private def getConstant (env : @& Kernel.Environment) (name : Name) :
    Except Kernel.Exception ConstantInfo :=
  match env.find? name with
  | some info => pure info
  | none => throw (.unknownConstant env name)

private structure BuildState where
  lctx : LocalContext := {}
  nextId : Nat := 0

private abbrev BuildM := StateT BuildState (Except Kernel.Exception)

private def freshLocal (name : Name) (type : Expr) (info : BinderInfo) : BuildM Expr := do
  let state ← get
  -- Input recursor types are closed kernel expressions. These temporary IDs do
  -- not occur in the result, so their spelling is not an output observable.
  let id : FVarId := ⟨.num (.str .anonymous "_casesOnRaw") state.nextId⟩
  set { state with lctx := state.lctx.mkLocalDecl id name type info,
                   nextId := state.nextId + 1 }
  return mkFVar id

private partial def openTelescope (type : Expr) (out : Array Expr := #[]) :
    BuildM (Array Expr × Expr) := do
  match type with
  | .forallE name domain body info =>
    let value ← freshLocal name domain info
    openTelescope (body.instantiate1 value) (out.push value)
  | _ => return (out, type)

private partial def terminal (type : Expr) : Expr :=
  match type with
  | .forallE _ _ body _ => terminal body
  | _ => type

private def isTypeFormer (ids : Array FVarId) (type : Expr) : Bool :=
  match type.getAppFn with
  | .fvar id => ids.contains id
  | _ => false

private partial def openMinor (type unit : Expr) (ids : Array FVarId) (main : FVarId)
    (isMain : Bool) (params nonrecursive : Array Expr := #[]) :
    BuildM (Array Expr × Array Expr × Expr) := do
  match type with
  | .forallE name domain body info =>
    let original ← freshLocal name domain info
    let head := (terminal domain).getAppFn
    let recursive := isTypeFormer ids (terminal domain)
    let selected ← if recursive && head.fvarId! != main then
        freshLocal name (piUnit domain unit) info
      else pure original
    let nonrecursive := if isMain && !recursive then nonrecursive.push original else nonrecursive
    -- Instantiation deliberately uses ORIGINAL even for a substituted PUnit local.
    openMinor (body.instantiate1 original) unit ids main isMain (params.push selected) nonrecursive
  | _ => return (params, nonrecursive, type)

private def minor (value unit star : Expr) (ids : Array FVarId) (main : FVarId)
    (isMain : Bool) : BuildM (Option Expr × Expr) := do
  let declaration := (← get).lctx.getFVar! value
  let (params, nonrecursive, result) ← openMinor declaration.type unit ids main isMain
  if isMain then
    let type := (← get).lctx.mkForall nonrecursive result
    let branch ← freshLocal declaration.userName type declaration.binderInfo
    let application := mkAppN branch nonrecursive
    return (some branch, (← get).lctx.mkLambda params application)
  else
    return (none, (← get).lctx.mkLambda params star)

private def usesUnsafe (env : @& Kernel.Environment) (type : Expr) : Bool :=
  (type.find? fun expression =>
    match expression with
    | .const name _ => (env.find? name).any ConstantInfo.isUnsafe
    | _ => false).isSome

/-- Port of native casesOn construction, not admission. Input is an existing
checked Kernel.Environment. Result retains actual guest AST values. Native
heartbeat/depth semantics and malformed unchecked environments are not modeled. -/
@[noinline] def construct (env : Kernel.Environment) (name : @& Name) :
    Except Kernel.Exception Declaration := do
  -- Keep the native owned-env ABI visible to borrow inference: this branch
  -- transfers the incoming environment directly into the typed error result.
  let info ← match env.find? name with
    | some info => pure info
    | none => throw (.unknownConstant env name)
  let .inductInfo inductiveValue := info
    | throw (.other ("error in 'casesOn' generation, '" ++ nativeNameString name ++ "' is not an inductive datatype"))
  let recName := Name.str name "rec"
  let recInfo ← getConstant env recName
  let .recInfo recursor := recInfo
    | throw (.other "Invalid casesOn input: expected recursor")
  let ((type, value), _) ← (do
    let (locals, result) ← openTelescope recursor.type
    let np := recursor.numParams
    let nm := recursor.numMotives
    let nn := recursor.numMinors
    let ni := recursor.numIndices
    let names := recursor.all.toArray
    unless locals.size == np + nm + nn + ni + 1 && names.size ≤ nm && names.contains name do
      throw (.other "Invalid casesOn input: recursor telescope")
    let levels := recursor.levelParams.map mkLevelParam
    let elim := if recursor.levelParams.length == inductiveValue.levelParams.length then Level.zero else levels.head!
    let unit := mkConst ``PUnit [elim]
    let star := mkConst ``PUnit.unit [elim]
    let mut parameters := locals.extract 0 np
    let mut arguments := parameters
    let mut ids : Array FVarId := #[]
    let mut main : FVarId := ⟨.anonymous⟩
    for j in [:nm] do
      let value := locals[np + j]!
      ids := ids.push value.fvarId!
      if j < names.size && names[j]! == name then
        parameters := parameters.push value
        arguments := arguments.push value
        main := value.fvarId!
      else
        arguments := arguments.push (funUnit ((← get).lctx.getFVar! value).type unit)
    let indicesMajor := locals.extract (np + nm + nn) locals.size
    parameters := parameters ++ indicesMajor
    let mut index := 0
    for current in names do
      let currentInfo ← getConstant env current
      let .inductInfo currentInductive := currentInfo
        | throw (.other "Invalid casesOn input: mutual member")
      for _ in currentInductive.ctors do
        unless index < nn do throw (.other "Invalid casesOn input: minor count")
        let (parameter, argument) ← minor locals[np + nm + index]! unit star ids main (current == name)
        if let some parameter := parameter then parameters := parameters.push parameter
        arguments := arguments.push argument
        index := index + 1
    for remaining in [index:nn] do
      let (_, argument) ← minor locals[np + nm + remaining]! unit star ids main false
      arguments := arguments.push argument
    arguments := arguments ++ indicesMajor
    let context := (← get).lctx
    return (context.mkForall parameters result,
            context.mkLambda parameters (mkAppN (mkConst recName levels) arguments))
    : BuildM (Expr × Expr)).run {}
  let safety := if usesUnsafe env type || usesUnsafe env value then .unsafe else .safe
  return .defnDecl {
    name := Name.str name "casesOn", levelParams := recursor.levelParams,
    type, value, hints := .abbrev, safety, all := [Name.str name "casesOn"] }

end KernelCasesOnRaw
