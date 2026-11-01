import KernelCasesOnRaw
import Lean.Meta.Constructions.CasesOn
import Lean.Data.Json

open Lean
namespace RawCasesOnOracle
universe u
inductive Colour where
  | red | green | blue
structure Pair (α : Type u) where
  left : α
  right : α
inductive Box (α : Type u) : Type u where
  | wrap : α → Box α
inductive Sized (α : Type u) : Nat → Type u where
  | nil : Sized α 0
  | cons : α → Sized α n → Sized α (n + 1)
mutual
  inductive Ping where
    | stop : Nat → Ping
    | next : Pong → Ping
  inductive Pong where
    | next : Ping → Pong
end
inductive Rose where
  | node : List Rose → Rose
inductive ChoiceProp : Prop where
  | left | right
unsafe inductive UnsafeBox where
  | wrap : Nat → UnsafeBox

inductive Tree where
  | leaf | branch : (Nat → Tree) → Tree

def notInductive : Nat := 0


inductive AnnotatedField where
  | metadata | dependentLet | nondependentLet

def annotatedDeclaration (name : Name) (kind : AnnotatedField)
    (useIMax : Bool := false) : Declaration := Id.run do
  let u := mkLevelParam `u
  let rawU := if useIMax then Level.imax u u else Level.max u u
  let sort := mkSort rawU
  let marker : MData := {
    entries := [(`oracle.marker, .ofString "preserve-this-payload"),
                (`oracle.syntax, .ofSyntax (.node .none `oracle.payload #[.atom .none "opaque"]))] }
  let field := match kind with
    | .metadata => mkBVar 0
    | .dependentLet => mkLet `X sort (mkBVar 0) (mkBVar 0) false
    | .nondependentLet => mkLet `X sort (mkBVar 0) (mkBVar 1) true
  let field := mkMData marker field
  let ctorType := mkForall `alpha .implicit sort <|
    mkForall `markedField .instImplicit field <| mkApp (mkConst name [u]) (mkBVar 1)
  let ctorValue : Constructor := {
    name := Name.str name "wrap"
    type := ctorType }
  let indType : InductiveType := {
    name := name
    type := mkForall `alpha .implicit sort sort
    ctors := [ctorValue] }
  return .inductDecl [`u] 1 [indType] false

private def nameJson : Name → Json
  | .anonymous => .arr #[.str "anonymous"]
  | .str parent text => .arr #[.str "str", nameJson parent, .str text]
  | .num parent number => .arr #[.str "num", nameJson parent, .str (toString number)]

private def levelJson : Level → Json
  | .zero => .arr #[.str "zero"]
  | .succ value => .arr #[.str "succ", levelJson value]
  | .max left right => .arr #[.str "max", levelJson left, levelJson right]
  | .imax left right => .arr #[.str "imax", levelJson left, levelJson right]
  | .param name => .arr #[.str "param", nameJson name]
  | .mvar id => .arr #[.str "mvar", nameJson id.name]

private def binderJson : BinderInfo → Json
  | .default => .str "default"
  | .implicit => .str "implicit"
  | .strictImplicit => .str "strictImplicit"
  | .instImplicit => .str "instImplicit"

private partial def syntaxJson : Syntax → Except String Json
  | .missing => pure <| .arr #[.str "missing"]
  | .node .none kind args => do
    pure <| .arr #[.str "node", nameJson kind, .arr (← args.mapM syntaxJson)]
  | .atom .none text => pure <| .arr #[.str "atom", .str text]
  | _ => throw "Oracle refuses unsupported Syntax/SourceInfo; no textual fallback"

private def dataJson : DataValue → Except String Json
  | .ofString value => pure <| .arr #[.str "string", .str value]
  | .ofBool value => pure <| .arr #[.str "bool", .bool value]
  | .ofName value => pure <| .arr #[.str "name", nameJson value]
  | .ofNat value => pure <| .arr #[.str "nat", .str (toString value)]
  | .ofInt value => pure <| .arr #[.str "int", .str (toString value)]
  | .ofSyntax value => do pure <| .arr #[.str "syntax", ← syntaxJson value]

private partial def exprJson (expression : Expr) (depth : Nat := 0) : Except String Json := do
  if depth > 256 then throw "Oracle raw expression serialization depth limit"
  let child := fun value => exprJson value (depth + 1)
  match expression with
  | .bvar index => pure <| .arr #[.str "bvar", .str (toString index)]
  | .fvar id => pure <| .arr #[.str "fvar", nameJson id.name]
  | .mvar id => pure <| .arr #[.str "mvar", nameJson id.name]
  | .sort level => pure <| .arr #[.str "sort", levelJson level]
  | .const name levels => pure <| .arr #[.str "const", nameJson name, .arr (levels.map levelJson).toArray]
  | .app function argument => pure <| .arr #[.str "app", ← child function, ← child argument]
  | .lam name type body info => pure <| .arr #[.str "lam", nameJson name, binderJson info, ← child type, ← child body]
  | .forallE name type body info => pure <| .arr #[.str "forall", nameJson name, binderJson info, ← child type, ← child body]
  | .letE name type value body nondep =>
    pure <| .arr #[.str "let", nameJson name, .bool nondep, ← child type, ← child value, ← child body]
  | .lit (.natVal value) => pure <| .arr #[.str "nat", .str (toString value)]
  | .lit (.strVal value) => pure <| .arr #[.str "string", .str value]
  | .mdata metadata body => do
    let entries ← metadata.entries.mapM fun (name, value) => do
      pure <| Json.arr #[nameJson name, ← dataJson value]
    pure <| .arr #[.str "mdata", .arr entries.toArray, ← child body]
  | .proj name index body => pure <| .arr #[.str "proj", nameJson name, .str (toString index), ← child body]

private def declarationJson (value : DefinitionVal) : Except String Json := do
  unless value.hints == .abbrev do throw "Expected native abbreviation"
  return .mkObj [("name", nameJson value.name),
    ("levelParams", .arr (value.levelParams.map nameJson).toArray),
    ("type", ← exprJson value.type), ("value", ← exprJson value.value),
    ("hints", .str "abbrev"), ("safety", .str (if value.safety == .safe then "safe" else if value.safety == .unsafe then "unsafe" else "partial")),
    ("all", .arr (value.all.map nameJson).toArray)]

private def fromStringExcept {α} (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

private def successDecl (value : Except Kernel.Exception Declaration) : IO DefinitionVal :=
  match value with
  | .ok (.defnDecl result) => pure result
  | _ => throw <| IO.userError "Expected native casesOn definition result"

private def compareCase (input : Kernel.Environment) (name : Name) (label : String)
    (checkedInput : Bool) : IO Unit := do
  let native ← successDecl (mkCasesOnImp input name)
  let port ← successDecl (KernelCasesOnRaw.construct input name)
  unless native.name == port.name && native.levelParams == port.levelParams &&
      native.type.equal port.type && native.value.equal port.value &&
      native.hints == port.hints && native.safety == port.safety && native.all == port.all do
    throw <| IO.userError ("Native full casesOn mismatch: " ++ label)
  let nativeOutput ← fromStringExcept <| declarationJson native
  let portOutput ← fromStringExcept <| declarationJson port
  unless nativeOutput == portOutput do throw <| IO.userError "Raw AST encodings differ"
  let recursorType ← match input.find? (Name.str name "rec") with
    | some (.recInfo value) => fromStringExcept <| exprJson value.type
    | _ => throw <| IO.userError "Missing actual recursor input"
  -- Existing frontend roots already have casesOn; native-admitted dynamic
  -- fixtures deliberately do not, so each output can be checked independently.
  let canCheck := (input.find? (Name.str name "casesOn")).isNone
  if canCheck then
    match input.addDeclCore 0 0 (.defnDecl native) none,
          input.addDeclCore 0 0 (.defnDecl port) none with
    | .ok _, .ok _ => pure ()
    | _, _ => throw <| IO.userError "Native output kernel checking failed"
  IO.println <| (Json.mkObj [("case", .str label), ("scope", .str (if checkedInput then "native-admitted-input" else "unchecked-carrier")),
    ("status", .str "passed"), ("outputKernelChecked", .bool canCheck),
    ("inputRecursorType", recursorType), ("native", nativeOutput), ("port", portOutput)]).compress

private def compareErrors (input : Kernel.Environment) (name : Name) (label : String) : IO Unit := do
  let native := mkCasesOnImp input name
  let port := KernelCasesOnRaw.construct input name
  let (kind, message) ← match native, port with
    | .error (.unknownConstant _ left), .error (.unknownConstant _ right) => do
      unless left == name && right == name do throw <| IO.userError "UnknownConstant Name mismatch"
      pure ("unknownConstant", "")
    | .error (.other left), .error (.other right) => do
      unless left == right do throw <| IO.userError "Native error message mismatch"
      pure ("other", left)
    | _, _ => throw <| IO.userError "Native typed error mismatch"
  IO.println <| (Json.mkObj [("case", .str label), ("status", .str "passed"),
    ("error", .str kind), ("name", nameJson name), ("message", .str message)]).compress

end RawCasesOnOracle

open RawCasesOnOracle in
def main : IO Unit := do
  unless Lean.githash == "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" do
    throw <| IO.userError "Pinned native producer mismatch"
  Lean.initSearchPath (← Lean.findSysroot)
  let base ← Lean.importModules #[{module := `RawCasesOnOracle}] {}
  let kernel := base.toKernelEnv
  IO.println <| (Lean.Json.mkObj [("schema", .str "raw-cases-on-native-oracle/1"), ("leanCommit", .str Lean.githash)]).compress
  for suffix in ["Colour", "Pair", "Box", "Sized", "Ping", "Pong", "Rose", "ChoiceProp", "UnsafeBox", "Tree"] do
    compareCase kernel (Name.str `RawCasesOnOracle suffix) suffix true
  for (suffix, kind, useIMax) in [("AnnotatedMetadata", AnnotatedField.metadata, false),
      ("AnnotatedDependentLet", AnnotatedField.dependentLet, false),
      ("AnnotatedNondependentLet", AnnotatedField.nondependentLet, false),
      ("AnnotatedIMax", AnnotatedField.metadata, true)] do
    let name := Name.str `RawCasesOnOracle suffix
    let input ← match kernel.addDeclCore 0 0 (annotatedDeclaration name kind useIMax) none with
      | .ok input => pure input
      | .error _ => throw <| IO.userError ("Native annotation input admission failed: " ++ suffix)
    compareCase input name suffix true

  compareErrors kernel (Name.str `RawCasesOnOracle "missing") "missing"
  for (label, name) in [("empty-component", Name.str .anonymous ""),
      ("quoted-component", Name.str (Name.str .anonymous "a.b") "x y"),
      ("numeric-component", Name.num (Name.str .anonymous "oracle") 37),
      ("unicode-component", Name.str (Name.str .anonymous "λ.🦉") "with space λ")] do
    let axiomDeclaration : Declaration := .axiomDecl { name, levelParams := [], type := mkSort .zero, isUnsafe := false }
    let input ← match kernel.addDeclCore 0 0 axiomDeclaration none with
      | .ok input => pure input
      | .error _ => throw <| IO.userError ("Native error-name input admission failed: " ++ label)
    compareErrors input name label
