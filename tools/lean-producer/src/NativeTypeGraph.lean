import Lean.Meta.Check
import Lean.Meta.ExprDefEq
import Lean.Compiler.LCNF.ToImpureType
import Lean.Compiler.IR.ToIRType
import Lean.Elab.Deriving.Inhabited
import NativeEntryTransport

/-!
Isolated automatic logical datatype discovery. Not imported by the published v2
producer, not a bundle/entry admission change, and not JVM allocation authority.
Product digests are explicit caller-supplied claims: a future source/artifact
pipeline must independently authenticate them and this producer's own cohort.
-/
open Lean

namespace NativeTypeGraph

/-- Module Name -> exact compiled defining-product SHA-256. Missing origins fail.
    This lookup supplies provenance claims; it does not authenticate itself. -/
abbrev ModuleProducts := Name → Option String

structure Discovery where
  logical : Json
  layouts : Json
  /-- Canonical native Exprs aligned with the deduplicated logical root catalog.
      Internal producer data; neither serialized host values nor authority. -/
  canonicalRoots : Array Expr

private structure ClosedField where
  type : Expr
  actualType : Expr
  descriptor : Json
  deriving Inhabited

private structure Pending where
  type : Expr
  info : InductiveVal
  moduleName : Name
  universes : Array Nat
  arguments : Array Json
  argumentRefs : Array Nat
  fieldsRefs : Array Nat := #[]
  definition? : Option Json := none
  closedFields : Array (Array ClosedField) := #[]
  deriving Inhabited

private structure State where
  nodes : Array Pending := #[]
  keys : Std.HashMap Expr Nat := {}
  builtinFamilies : Array Name := #[]
  visits : Nat := 0
  edges : Nat := 0
  constructors : Nat := 0
  nameUnits : Nat := 0

private abbrev DiscoverM := StateT State MetaM

private def fail {α} (reason : String) : DiscoverM α :=
  throwError "TypeGraph: {reason}"

private def tick (edges : Nat := 0) : DiscoverM Unit := do
  let s ← get
  unless s.visits < 8192 && s.edges + edges ≤ 4096 do fail "descriptor/edge budget"
  set { s with visits := s.visits + 1, edges := s.edges + edges }

private def edge! (n : Nat) : DiscoverM Unit := do
  let s ← get
  unless s.edges + n ≤ 4096 do fail "edge budget"
  set { s with edges := s.edges + n }

private def closed! (e : Expr) : MetaM Unit := do
  unless !e.hasMVar && !e.hasFVar && !e.hasLevelParam && !e.hasLooseBVars do
    throwError "TypeGraph: open/dependent type or universe"

private def unique [BEq α] (xs : Array α) : Array α :=
  xs.foldl (fun out x => if out.contains x then out else out.push x) #[]

private def nameJson := NativeEntryTransport.nameJson

private def checkedName (name : Name) (nonanonymous : Bool := true) : DiscoverM Json := do
  if nonanonymous && name.isAnonymous then fail "anonymous declaration/module Name"
  let mut n := name
  let mut depth := 0
  let mut units := 0
  repeat
    unless depth < 64 do fail "Name depth budget"
    depth := depth + 1
    match n with
    | .anonymous => break
    | .str p s =>
      unless s.utf8ByteSize ≤ 4096 do fail "Name leaf budget"
      let size : Nat := s.toList.foldl (fun count c => count + if c.toNat > 65535 then 2 else 1) 0
      unless size ≤ 1024 do fail "Name leaf UTF-16 budget"
      units := units + size
      n := p
    | .num p v =>
      unless v ≤ 18446744073709551615 do fail "numeric Name UInt64 overflow"
      units := units + (toString v).length
      n := p
  let s ← get
  unless s.nameUnits + units ≤ 65536 do fail "aggregate Name text budget"
  set { s with nameUnits := s.nameUnits + units }
  return nameJson name

private def normalizedLevels (levels : List Level) : DiscoverM (List Level × Array Nat) := do
  unless levels.length ≤ 32 do fail "universe argument count"
  let mut out := []
  let mut values := #[]
  for u in levels do
    unless !u.hasMVar && !u.hasParam do fail "open universe"
    -- Bound normalization input as well as its eventual closed numeral.
    let mut todo := #[u]
    let mut work := 0
    while !todo.isEmpty do
      unless work < 8192 do fail "universe normalization work"
      work := work + 1
      let item := todo.back!
      todo := todo.pop
      unless item.depth ≤ 512 do fail "universe AST depth"
      match item with
      | .zero => pure ()
      | .succ p => todo := todo.push p
      | .max a b | .imax a b => todo := todo.push a |>.push b
      | _ => fail "open universe"
    let normalized := u.normalize
    let some value := normalized.toNat | fail "universe does not normalize to a closed natural"
    unless value ≤ 255 do fail "universe numeral budget"
    out := out ++ [normalized]
    values := values.push value
  return (out, values)

private def boundedExpr! (root : Expr) : DiscoverM Unit := do
  let mut todo := #[(root, 0)]
  let mut work := 0
  while !todo.isEmpty do
    unless work < 8192 do fail "native type expression work"
    work := work + 1
    let (e, depth) := todo.back!
    todo := todo.pop
    unless depth < 256 do fail "native type expression depth"
    match e with
    | .const _ levels => discard <| normalizedLevels levels
    | .sort level => discard <| normalizedLevels [level]
    | .app f a => todo := todo.push (f, depth + 1) |>.push (a, depth + 1)
    | .forallE _ a b _ | .lam _ a b _ =>
      todo := todo.push (a, depth + 1) |>.push (b, depth + 1)
    | .letE _ t v b _ =>
      todo := todo.push (t, depth + 1) |>.push (v, depth + 1) |>.push (b, depth + 1)
    | .mdata _ b | .proj _ _ b => todo := todo.push (b, depth + 1)
    | _ => pure ()

private def originModule (name : Name) : DiscoverM Name := do
  let env ← getEnv
  let moduleName ← match env.getModuleIdxFor? name with
    | some index =>
      match env.allImportedModuleNames[index.toNat]? with
      | some moduleName => pure moduleName
      | none => fail "missing native defining-module index"
    | none => pure env.mainModule
  discard <| checkedName moduleName
  return moduleName

private def origin (products : ModuleProducts) (moduleName : Name) : DiscoverM Json := do
  let some sha := products moduleName | fail "missing defining-module product digest"
  unless sha.length == 64 && sha.toList.all (fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) do fail "noncanonical product SHA-256"
  return Json.mkObj [("module", nameJson moduleName), ("productSha256", toJson sha)]

private def leaf (kind : String) : Json := Json.mkObj [("kind", toJson kind)]
private def refJson (id : Nat) : Json := Json.mkObj [("kind", toJson "nominal"), ("id", toJson id)]

private structure TypeResult where
  type : Expr
  descriptor : Json
  refs : Array Nat := #[]
  deriving Inhabited

private def primitiveTypes : Array (Name × Json) :=
  #[( ``Nat, leaf "nat"), (``Int, leaf "int"), (``Bool, leaf "bool"),
    (``String, leaf "string"), (``Unit, leaf "unit"), (``Char, leaf "char"),
    (``ByteArray, leaf "bytes")] ++
  (#[( ``UInt8, 8, false), (``UInt16, 16, false), (``UInt32, 32, false), (``UInt64, 64, false),
     (``Int8, 8, true), (``Int16, 16, true), (``Int32, 32, true), (``Int64, 64, true)]).map
    (fun (n, bits, signed) => (n, Json.mkObj [("kind", toJson "machine-int"),
      ("bits", toJson bits), ("signed", toJson signed)])) ++
  #[( ``USize, Json.mkObj [("kind", toJson "word"), ("signed", toJson false)]),
    (``ISize, Json.mkObj [("kind", toJson "word"), ("signed", toJson true)]),
    (``Float, Json.mkObj [("kind", toJson "float"), ("bits", toJson (64 : Nat))]),
    (``Float32, Json.mkObj [("kind", toJson "float"), ("bits", toJson (32 : Nat))])]

private def container? (name : Name) : Option (String × Array String) :=
  if name == ``Prod then some ("product", #["first", "second"])
  else if name == ``Sum then some ("sum", #["left", "right"])
  else if name == ``Except then some ("except", #["error", "value"])
  else if name == ``Option then some ("option", #["element"])
  else if name == ``List then some ("list", #["element"])
  else if name == ``Array then some ("array", #["element"])
  else none

private def specialRuntime (name : Name) : Bool :=
  -- These heads have runtime/lifecycle semantics beyond ordinary constructor
  -- storage. Opaque/function/proof-bearing kinds are rejected independently.
  Compiler.LCNF.isRuntimeBuiltinType name ||
    [``ST.Ref, ``IO.Promise, ``IO.FS.Handle,
     ``Lean.Name, ``Lean.Level, ``Lean.Expr].contains name

private def parameterTypes! (info : InductiveVal) (levels : List Level)
    (args : Array Expr) : MetaM Unit := do
  let mut telescope := info.type.instantiateLevelParams info.levelParams levels
  for arg in args do
    let .forallE _ domain body _ ← Meta.whnf telescope
      | throwError "TypeGraph: parameter telescope mismatch"
    let domain ← Meta.whnf domain
    unless domain.isSort do throwError "TypeGraph: term/type-former-valued parameter"
    let argType ← Meta.inferType arg
    unless ← Meta.isDefEq argType domain do throwError "TypeGraph: parameter sort mismatch"
    telescope := body.instantiate1 arg
  let result ← Meta.whnf telescope
  unless result.isSort do throwError "TypeGraph: incomplete inductive application"

private partial def infer (type : Expr) (depth : Nat) : DiscoverM TypeResult := do
  unless depth < 32 do fail "inline type depth"
  tick
  liftM <| closed! type
  boundedExpr! type
  let type ← liftM <| Meta.withTransparency .default (Meta.whnf type)
  liftM <| closed! type
  if ← liftM <| Meta.isProp type then fail "proof-valued field/parameter"
  for (name, descriptor) in primitiveTypes do
    if ← liftM <| Meta.withTransparency .default (Meta.isDefEq type (mkConst name)) then
      return { type := mkConst name, descriptor }
  match type with
  | .sort _ => fail "type former is not a value"
  | .forallE .. => fail "function-valued data"
  | _ => pure ()
  let .const name levels := type.getAppFn | fail "unknown type head"
  let args := type.getAppArgs
  let (levels, universes) ← normalizedLevels levels
  if let some (kind, labels) := container? name then
    unless args.size == labels.size do fail "builtin container arity"
    edge! args.size
    let mut entries := [("kind", toJson kind)]
    let mut canonicalArgs := #[]
    let mut refs := #[]
    for i in [:args.size] do
      let child ← infer args[i]! (depth + 1)
      entries := entries ++ [(labels[i]!, child.descriptor)]
      canonicalArgs := canonicalArgs.push child.type
      refs := refs ++ child.refs
    unless name == ``Array do
      modify fun s => { s with builtinFamilies := unique (s.builtinFamilies.push name) }
    let canonical := mkAppN (mkConst name levels) canonicalArgs
    unless ← liftM <| Meta.isDefEq type canonical do fail "native builtin reconstruction mismatch"
    return { type := canonical, descriptor := Json.mkObj entries, refs := unique refs }
  if specialRuntime name then fail "special runtime type has no nominal profile"
  let some (.inductInfo info) := (← getEnv).find? name | fail "opaque/noninductive type"
  unless !info.isUnsafe && !info.isReflexive && info.numIndices == 0 do
    fail "unsafe/indexed/reflexive inductive"
  -- numNested is separate from the user mutual block: compiler auxiliaries
  -- must not disqualify Tree with List/Array recursive fields.
  unless info.all == [name] && info.numNested ≤ 256 do fail "user mutual inductive or nested budget"
  unless info.numParams ≤ 64 && args.size == info.numParams &&
      info.ctors.length > 0 && info.ctors.length ≤ 1024 do fail "inductive arity/constructor budget"
  unless info.levelParams.length == levels.length do fail "inductive universe arity"
  liftM <| parameterTypes! info levels args
  let mut arguments := #[]
  let mut canonicalArgs := #[]
  let mut argumentRefs := #[]
  for arg in args do
    let child ← infer arg (depth + 1)
    arguments := arguments.push child.descriptor
    canonicalArgs := canonicalArgs.push child.type
    argumentRefs := argumentRefs ++ child.refs
  let canonical := mkAppN (mkConst name levels) canonicalArgs
  unless ← liftM <| Meta.isDefEq type canonical do fail "native nominal reconstruction mismatch"
  edge! 1
  if let some id := (← get).keys[canonical]? then
    return { type := canonical, descriptor := refJson id, refs := #[id] }
  let s ← get
  unless s.nodes.size < 256 && s.constructors + info.ctors.length ≤ 1024 do
    fail "nominal definition/constructor budget"
  let moduleName ← originModule name
  let s ← get
  let id := s.nodes.size
  -- Register before walking constructors; recursive fields become references.
  let pending : Pending := {
    type := canonical
    info := info
    moduleName := moduleName
    universes := universes
    arguments := arguments
    argumentRefs := unique argumentRefs }
  set { s with
    nodes := s.nodes.push pending
    keys := s.keys.insert canonical id
    constructors := s.constructors + info.ctors.length }
  return { type := canonical, descriptor := refJson id, refs := #[id] }

private def constructorFields (p : Pending) (name : Name) (index : Nat) : MetaM (Array (Name × Expr)) := do
  let some (.ctorInfo ctor) := (← getEnv).find? name
    | throwError "TypeGraph: missing native constructor"
  unless !ctor.isUnsafe && ctor.induct == p.info.name && ctor.cidx == index &&
      ctor.numParams == p.info.numParams && ctor.numFields ≤ 64 &&
      ctor.levelParams.length == p.type.getAppFn.constLevels!.length do
    throwError "TypeGraph: constructor family/telescope mismatch"
  let type := ctor.type.instantiateLevelParams ctor.levelParams p.type.getAppFn.constLevels!
  let type ← Meta.instantiateForall type p.type.getAppArgs
  Meta.forallTelescope type fun fields result => do
    unless fields.size == ctor.numFields do throwError "TypeGraph: constructor field count mismatch"
    closed! result
    unless ← Meta.isDefEq result p.type do throwError "TypeGraph: constructor result mismatch"
    let mut out := #[]
    for f in fields do
      let domain ← Meta.inferType f
      -- Check before reducing as well: no previous value binder may occur.
      closed! domain
      let domain ← Meta.withTransparency .default (Meta.whnf domain)
      closed! domain
      if ← Meta.isProp domain then throwError "TypeGraph: proof-bearing constructor"
      out := out.push ((← f.fvarId!.getDecl).userName, domain)
    return out

private def closure (nodes : Array Pending) (seed : Array Nat) : Array Nat := Id.run do
  let mut todo := seed
  let mut seen := #[]
  while !todo.isEmpty do
    let id := todo.back!
    todo := todo.pop
    if seen.contains id then continue
    seen := seen.push id
    let p := nodes[id]!
    todo := todo ++ p.argumentRefs ++ p.fieldsRefs
  return seen

private def regular! (nodes : Array Pending) : DiscoverM Unit := do
  let mut complete : Array Nat := #[]
  while complete.size < nodes.size do
    let mut progress := false
    for id in [:nodes.size] do
      if complete.contains id then continue
      let p := nodes[id]!
      if p.argumentRefs.contains id then fail "recursive closed argument"
      if (p.argumentRefs ++ p.fieldsRefs).all (fun child => child == id || complete.contains child) then
        complete := complete.push id
        progress := true
    unless progress do fail "nonregular/mutual nominal dependency cycle"
  for id in [:nodes.size] do
    let p := nodes[id]!
    let allowed := closure nodes p.argumentRefs
    for child in closure nodes (p.argumentRefs ++ p.fieldsRefs) do
      if child != id && nodes[child]!.info.name == p.info.name && !allowed.contains child then
        fail "changed-parameter recursive application"

private def fieldLayoutJson := NativeEntryTransport.fieldLayoutJson

private def familyLayout (name : Name) : MetaM Json := do
  let some (.inductInfo info) := (← getEnv).find? name
    | throwError "TypeGraph: missing layout family"
  unless info.ctors.length ≤ 1024 do throwError "TypeGraph: layout constructor budget"
  let mut constructors := #[]
  for ctorName in info.ctors do
    let layout ← Compiler.LCNF.getCtorLayout ctorName
    unless layout.fieldInfo.size ≤ 64 do throwError "TypeGraph: declaration layout field budget"
    let i := layout.ctorInfo
    constructors := constructors.push <| Json.mkObj [
      ("constructor", nameJson ctorName),
      ("ctorInfo", Json.mkObj [("name", nameJson i.name), ("cidx", toJson i.cidx),
        ("size", toJson i.size), ("usize", toJson i.usize), ("ssize", toJson i.ssize)]),
      ("fields", Json.arr (layout.fieldInfo.map fieldLayoutJson))]
  let impure ← Compiler.LCNF.nameToImpureType name
  let trivial ← Compiler.LCNF.hasTrivialImpureStructure? name
  let trivial := trivial.map fun t => Json.mkObj [("constructor", nameJson t.ctorName),
    ("fieldIndex", toJson t.fieldIdx), ("numParams", toJson t.numParams)]
  return Json.mkObj [("typeName", nameJson name), ("irType", toJson (IR.toIRType impure)),
    ("trivialStructure", toJson trivial), ("constructors", Json.arr constructors)]

private def classifyM (roots : Array Expr) : DiscoverM (Array TypeResult) := do
  unless roots.size > 0 && roots.size ≤ 1024 do fail "root count"
  let mut rootTypes : Array TypeResult := #[]
  for root in roots do
    liftM <| closed! root
    boundedExpr! root
    liftM <| Meta.check root .default
    let r ← infer root 0
    unless rootTypes.any (fun previous => previous.descriptor == r.descriptor) do
      rootTypes := rootTypes.push r
  let mut cursor := 0
  while cursor < (← get).nodes.size do
    let p := (← get).nodes[cursor]!
    let mut constructors := #[]
    let mut fieldsRefs := #[]
    let mut closedFields := #[]
    for index in [:p.info.ctors.length] do
      let name := p.info.ctors[index]!
      let fields ← liftM <| constructorFields p name index
      let ctorName ← checkedName name
      let mut values := #[]
      let mut closedValues := #[]
      for (binder, domain) in fields do
        let fieldName ← checkedName binder false
        let value ← infer domain 0
        values := values.push <| Json.mkObj [("name", fieldName), ("type", value.descriptor)]
        let closedValue : ClosedField := {
          type := value.type
          actualType := domain
          descriptor := value.descriptor }
        closedValues := closedValues.push closedValue
        fieldsRefs := fieldsRefs ++ value.refs
      constructors := constructors.push <| Json.mkObj [("name", ctorName), ("fields", Json.arr values)]
      closedFields := closedFields.push closedValues
    -- Internal shape only: no origin object is manufactured before a real
    -- product lookup. This incomplete object is never returned as a graph.
    let definition := Json.mkObj [("id", toJson cursor),
      ("name", ← checkedName p.info.name), ("universes", toJson p.universes),
      ("arguments", Json.arr p.arguments), ("constructors", Json.arr constructors)]
    modify fun s => { s with nodes := s.nodes.set! cursor { p with
      fieldsRefs := unique fieldsRefs, definition? := some definition, closedFields } }
    cursor := cursor + 1
  regular! (← get).nodes
  return rootTypes

private def encodedType (type : Expr) : DiscoverM Json :=
  match NativeEntryTransport.encodeType type with
  | .ok value => pure value
  | .error reason => fail s!"native type AST: {reason}"

private def closedIR (type : Expr) : MetaM Json := do
  let lcnf ← Compiler.LCNF.toLCNFType type
  let mono ← Compiler.LCNF.toMonoType lcnf
  let impure ← Compiler.LCNF.toImpureType mono
  return toJson (IR.toIRType impure)

private def inventoryM (roots : Array Expr) : DiscoverM Json := do
  let rootTypes ← classifyM roots
  let s ← get
  let modules := unique (s.nodes.map (·.moduleName))
  let types ← rootTypes.mapM (fun r => encodedType r.type)
  let document := Json.mkObj [("schema", toJson "lean-jvm-type-origin-inventory/1"),
    ("scope", toJson "advisory-no-type-authority"),
    ("requiredModules", Json.arr (modules.map nameJson)),
    ("rootTypes", Json.arr types), ("nominalDefinitions", toJson s.nodes.size)]
  unless document.compress.utf8ByteSize ≤ 1048576 do fail "encoded origin inventory byte budget"
  return document

private def discoverM (roots : Array Expr) (products : ModuleProducts) : DiscoverM Discovery := do
  let rootTypes ← classifyM roots
  let s ← get
  let mut definitions := #[]
  for p in s.nodes do
    let provenance ← origin products p.moduleName
    definitions := definitions.push (p.definition?.get!.setObjVal! "origin" provenance)
  let logical := Json.mkObj [("schema", toJson "lean-jvm-type-graph/3"),
    ("roots", Json.arr (rootTypes.map (·.descriptor))), ("definitions", Json.arr definitions)]
  unless logical.compress.utf8ByteSize ≤ 1048576 do fail "encoded logical graph byte budget"
  let mut applications := #[]
  let mut closedFields := #[]
  let mut names := s.builtinFamilies
  for id in [:s.nodes.size] do
    let p := s.nodes[id]!
    names := unique (names.push p.info.name)
    applications := applications.push <| Json.mkObj [("definition", toJson id),
      ("nativeType", ← encodedType p.type), ("irType", ← liftM <| closedIR p.type)]
    let mut constructors := #[]
    for index in [:p.info.ctors.length] do
      let ctorName := p.info.ctors[index]!
      let layout ← liftM <| Compiler.LCNF.getCtorLayout ctorName
      let fields := p.closedFields[index]!
      unless layout.ctorInfo.name == ctorName && layout.ctorInfo.cidx == index &&
          layout.fieldInfo.size == fields.size do fail "closed field/declaration layout correspondence"
      let mut observations := #[]
      for fieldIndex in [:fields.size] do
        let f := fields[fieldIndex]!
        unless ← liftM <| Meta.withTransparency .default (Meta.isDefEq f.actualType f.type) do
          fail "closed field native DefEq mismatch"
        observations := observations.push <| Json.mkObj [
          ("field", toJson fieldIndex), ("logicalType", f.descriptor),
          ("typeCheck", Json.mkObj [("algorithm", toJson "Lean.Meta.isDefEq"),
            ("transparency", toJson "default"),
            ("actualType", ← encodedType f.actualType), ("expectedType", ← encodedType f.type)]),
          ("closedIRType", ← liftM <| closedIR f.type),
          ("genericFieldIndex", toJson fieldIndex),
          ("genericFieldInfo", fieldLayoutJson layout.fieldInfo[fieldIndex]!)]
      constructors := constructors.push <| Json.mkObj [("constructor", nameJson ctorName),
        ("constructorIndex", toJson index), ("fields", Json.arr observations)]
    closedFields := closedFields.push <| Json.mkObj [("definition", toJson id),
      ("constructors", Json.arr constructors)]
  let families ← liftM <| names.mapM familyLayout
  let mut nativeRoots := #[]
  for index in [:rootTypes.size] do
    let r := rootTypes[index]!
    nativeRoots := nativeRoots.push <| Json.mkObj [("root", toJson index),
      ("nativeType", ← encodedType r.type), ("irType", ← liftM <| closedIR r.type)]
  let layouts := Json.mkObj [("schema", toJson "lean-jvm-native-layout-observations/4"),
    ("scope", toJson "observed-not-admitted"),
    ("rootTypes", Json.arr nativeRoots), ("applications", Json.arr applications),
    ("closedFields", Json.arr closedFields), ("families", Json.arr families)]
  unless layouts.compress.utf8ByteSize ≤ 1048576 do fail "encoded layout observation byte budget"
  return { logical, layouts, canonicalRoots := rootTypes.map (·.type) }

/-- Classify the complete supported type/constructor closure and report all
    required native defining modules without product claims or an admitted
    graph. This uses exactly the full discovery classifier and rejects the same
    unsupported logical forms. It is advisory, not a one-at-a-time failure probe. -/
def inventoryOrigins (roots : Array Expr) : MetaM Json := do
  let (result, _) ← (inventoryM roots).run {}
  return result

/-- Discover a finite closed proof-free logical graph in the actual native Meta
    Environment and separately observe persisted compiler layouts and closed
    field lowering. Product claims still require independent source custody;
    no public cohort or allocation authority is issued. -/
def discover (roots : Array Expr) (products : ModuleProducts) : MetaM Discovery := do
  let (result, _) ← (discoverM roots products).run {}
  return result

end NativeTypeGraph
