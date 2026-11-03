module

public import NativeTypeGraph
public import Lean.Compiler.LCNF.ToDecl
public import Lean.Compiler.ImplementedByAttr
public import Lean.ImportingFlag
public import Lean.Util.Path
public import Lean.Meta.AppBuilder
meta import Lean.Elab.Deriving.Inhabited

public section

/-!
Candidate native v3 entry observations plus the private closed-type probe facade.
This module does not issue source/cache/artifact capabilities or register a
producer cohort. No published old source/binary pair authorizes this new code.
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

private def ioPayload? (type : Expr) : MetaM (Option Expr) := do
  let payload ← Meta.mkFreshExprMVar (some (mkSort (.succ .zero)))
  if ← Meta.withTransparency .default (Meta.isDefEq type (mkApp (mkConst ``IO) payload)) then
    let payload ← instantiateMVars payload
    unless !payload.hasMVar && !payload.hasFVar && !payload.hasLevelParam && !payload.hasLooseBVars do
      throwError "NominalEntry: open/dependent IO payload"
    return some payload
  return none

private structure Signature where
  arguments : Array Expr
  result : Expr
  io : Bool
  deriving Inhabited

private partial def signatureOf (type : Expr) (arguments : Array Expr := #[]) : MetaM Signature := do
  if let some payload ← ioPayload? type then return { arguments, result := payload, io := true }
  let type ← Meta.withTransparency .default (Meta.whnf type)
  match type with
  | .forallE binder domain body bi =>
    unless bi == .default && arguments.size < 64 do throwError "NominalEntry: binder/arity unsupported"
    unless !domain.hasMVar && !domain.hasFVar && !domain.hasLevelParam && !domain.hasLooseBVars do
      throwError "NominalEntry: dependent argument"
    Meta.withLocalDecl binder bi domain fun value =>
      signatureOf (body.instantiate1 value) (arguments.push domain)
  | _ => return { arguments, result := type, io := false }

private structure Selected where
  name : Name
  kind : String
  actual : Expr
  signature : Signature
  deriving Inhabited

private def select (env : Environment) (name : Name) : MetaM Selected := do
  let some ci := env.find? name | throwError "NominalEntry: requested declaration absent"
  let kind ← match ci with
    | .defnInfo _ => pure "definition"
    | .opaqueInfo _ => pure "opaque"
    | _ => throwError "NominalEntry: unsupported ConstantInfo kind"
  unless ci.name == name && ci.levelParams.isEmpty && !ci.isUnsafe && !ci.isPartial &&
      !ci.type.hasMVar && !ci.type.hasFVar && !ci.type.hasLevelParam && !ci.type.hasLooseBVars do
    throwError "NominalEntry: identity/safety/closedness refusal"
  unless ← Compiler.LCNF.declIsNotUnsafe name do throwError "NominalEntry: unsafe or partial entry"
  unless !isExtern env name && (Compiler.getImplementedBy? env name).isNone &&
      (getInitFnNameFor? env name).isNone && !isIOUnitInitFn env name && !isIOUnitBuiltinInitFn env name do
    throwError "NominalEntry: extern/redirect/initializer entry refusal"
  return { name, kind, actual := ci.type, signature := ← signatureOf ci.type }

private def jsonValue {α} (value : Except String α) : MetaM α :=
  match value with
  | .ok value => pure value
  | .error reason => throwError "NominalEntry: malformed generated type metadata: {reason}"

private def primitiveName (type : Json) : MetaM (Option Name) := do
  let kind ← jsonValue (type.getObjValAs? String "kind")
  for (k, n) in #[("nat", ``Nat), ("int", ``Int), ("bool", ``Bool), ("string", ``String),
                  ("unit", ``Unit), ("char", ``Char), ("bytes", ``ByteArray)] do
    if kind == k then return some n
  if kind == "machine-int" then
    let bits ← jsonValue (type.getObjValAs? Nat "bits")
    let signed ← jsonValue (type.getObjValAs? Bool "signed")
    for (b, unsigned, negative) in #[(8, ``UInt8, ``Int8), (16, ``UInt16, ``Int16),
                                     (32, ``UInt32, ``Int32), (64, ``UInt64, ``Int64)] do
      if b == bits then return some (if signed then negative else unsigned)
    throwError "NominalEntry: machine integer width"
  if kind == "word" then return some (if ← jsonValue (type.getObjValAs? Bool "signed") then ``ISize else ``USize)
  if kind == "float" then
    let bits ← jsonValue (type.getObjValAs? Nat "bits")
    if bits == 32 then return some ``Float32
    if bits == 64 then return some ``Float
    throwError "NominalEntry: float width"
  return none

/-- Reconstruct in actual Meta, inferring builtin universes from checked child
    types. Generated logical metadata is not an arbitrary caller-supplied schema. -/
private partial def reconstruct (graph type : Json) (depth : Nat := 0) : MetaM Expr := do
  unless depth < 256 do throwError "NominalEntry: type reconstruction depth"
  if let some name ← primitiveName type then return mkConst name
  let kind ← jsonValue (type.getObjValAs? String "kind")
  if kind == "nominal" then
    let id ← jsonValue (type.getObjValAs? Nat "id")
    let definitions ← jsonValue (graph.getObjValAs? (Array Json) "definitions")
    unless id < definitions.size do throwError "NominalEntry: generated nominal reference"
    let d := definitions[id]!
    unless (← jsonValue (d.getObjValAs? Nat "id")) == id do throwError "NominalEntry: definition numbering"
    let name ← jsonValue (NativeEntryTransport.checkedName (← jsonValue (d.getObjVal? "name")))
    let universes ← jsonValue (d.getObjValAs? (Array Nat) "universes")
    let args ← jsonValue (d.getObjValAs? (Array Json) "arguments")
    unless universes.size ≤ 32 && universes.all (· ≤ 255) && args.size ≤ 64 do
      throwError "NominalEntry: generated nominal arity"
    let args ← args.mapM (fun arg => reconstruct graph arg (depth + 1))
    return mkAppN (mkConst name (universes.toList.map (·.toLevel))) args
  for (k, name, fields) in #[("product", ``Prod, #["first", "second"]),
      ("sum", ``Sum, #["left", "right"]), ("except", ``Except, #["error", "value"]),
      ("option", ``Option, #["element"]), ("list", ``List, #["element"]), ("array", ``Array, #["element"])] do
    if kind == k then
      let args ← fields.mapM fun field => do
        reconstruct graph (← jsonValue (type.getObjVal? field)) (depth + 1)
      return ← instantiateMVars (← Meta.mkAppM name args)
  throwError "NominalEntry: unsupported generated type kind"

private def rootIndex (roots : Array Expr) (type : Expr) : MetaM Nat := do
  for i in [:roots.size] do
    if ← Meta.withTransparency .default (Meta.isDefEq roots[i]! type) then return i
  throwError "NominalEntry: missing catalog root"

private def allDescriptors (graph : Json) : Except String (Array Json) := do
  let definitions ← graph.getObjValAs? (Array Json) "definitions"
  let mut todo ← graph.getObjValAs? (Array Json) "roots"
  for d in definitions do
    todo := todo ++ (← d.getObjValAs? (Array Json) "arguments")
    for c in ← d.getObjValAs? (Array Json) "constructors" do
      for f in ← c.getObjValAs? (Array Json) "fields" do todo := todo.push (← f.getObjVal? "type")
  let mut out := #[]
  let mut work := 0
  while !todo.isEmpty do
    unless work < 8192 do throw "special descriptor work budget"
    work := work + 1
    let t := todo.back!
    todo := todo.pop
    let kind ← t.getObjValAs? String "kind"
    if !out.contains t then out := out.push t
    let fields := if ["option", "list", "array"].contains kind then #["element"]
      else if kind == "product" then #["first", "second"]
      else if kind == "sum" then #["left", "right"]
      else if kind == "except" then #["error", "value"] else #[]
    for field in fields do todo := todo.push (← t.getObjVal? field)
  return out

private def runtimeWitnesses (graph : Json) (io : Bool) : MetaM Json := do
  let descriptors ← jsonValue (allDescriptors graph)
  let catalog ← descriptors.mapM fun descriptor => do
    return (descriptor, ← reconstruct graph descriptor)
  let mut types := #[]
  let mut builtins := #[]
  let mut comparisons := 0
  for (descriptor, type) in catalog do
    let kind ← jsonValue (descriptor.getObjValAs? String "kind")
    if ["nat", "int", "string", "machine-int", "word", "float", "char", "bytes", "array", "unit", "bool"].contains kind then
      types := types.push <| Json.mkObj [("type", descriptor), ("nativeType", ← encode type),
        ("irType", toJson (← NativeTypeGraph.observeIRType type))]
    if ["list", "option", "product", "sum", "except"].contains kind then
      unless builtins.size < 1024 do throwError "NominalWitness: closed builtin count"
      let family := type.getAppFn.constName!
      let some (.inductInfo info) := (← getEnv).find? family
        | throwError "NominalWitness: missing native builtin family"
      unless info.ctors.length ≤ 1024 do throwError "NominalWitness: builtin constructor budget"
      let mut constructors := #[]
      for index in [:info.ctors.length] do
        let name := info.ctors[index]!
        let fields ← NativeTypeGraph.observeConstructorFields type name index
        let layout ← Compiler.LCNF.getCtorLayout name
        unless layout.ctorInfo.name == name && layout.ctorInfo.cidx == index &&
            layout.fieldInfo.size == fields.size do
          throwError "NominalWitness: builtin telescope/layout correspondence"
        let mut observations := #[]
        for fieldIndex in [:fields.size] do
          let actual := fields[fieldIndex]!.2
          let mut matched? := none
          for (candidate, expected) in catalog do
            unless comparisons < 65536 do throwError "NominalWitness: field DefEq work budget"
            comparisons := comparisons + 1
            if ← Meta.withTransparency .default (Meta.isDefEq actual expected) then
              matched? := some (candidate, expected)
              break
          let some (logicalType, expected) := matched?
            | throwError "NominalWitness: builtin field absent from generated type closure"
          observations := observations.push <| Json.mkObj [
            ("field", toJson fieldIndex), ("logicalType", logicalType),
            ("typeCheck", Json.mkObj [("algorithm", toJson "Lean.Meta.isDefEq"),
              ("transparency", toJson "default"),
              ("actualType", ← encode actual), ("expectedType", ← encode expected)]),
            ("closedIRType", toJson (← NativeTypeGraph.observeIRType expected)),
            ("genericFieldIndex", toJson fieldIndex),
            ("genericFieldInfo", NativeEntryTransport.fieldLayoutJson layout.fieldInfo[fieldIndex]!)]
        constructors := constructors.push <| Json.mkObj [("constructor", NativeEntryTransport.nameJson name),
          ("constructorIndex", toJson index), ("fields", Json.arr observations)]
      builtins := builtins.push <| Json.mkObj [("type", descriptor), ("nativeType", ← encode type),
        ("irType", toJson (← NativeTypeGraph.observeIRType type)),
        ("family", NativeEntryTransport.nameJson family), ("constructors", Json.arr constructors)]
  let mut envelopes := #[]
  if io then
    for family in #[``EST.Out, ``IO.Error] do
      envelopes := envelopes.push (← NativeTypeGraph.observeFamilyLayout family)
  -- Native execution of the opaque platform primitive; never unfold its
  -- placeholder inhabitant in the kernel. Pinned Prelude + runtime/platform.cpp.
  let wordBits := System.Platform.numBits
  unless wordBits == 32 || wordBits == 64 do throwError "NominalWitness: unsupported native target word width"
  return Json.mkObj [("algorithm", toJson "Lean.Compiler.LCNF.toLCNFType/toMonoType/toImpureType"),
    ("specialTypes", Json.arr types), ("closedBuiltins", Json.arr builtins),
    ("ioFamilies", Json.arr envelopes),
    ("world", if io then toJson "canonical-erased-zero" else Json.null),
    ("target", Json.mkObj [("wordBits", toJson wordBits),
      ("wordBitsSource", toJson "System.Platform.numBits")])]

/-- Compiler-only complete witnesses in the current already-imported Environment.
    No callable lookup, request authority or source/artifact admission. -/
def observeTypeWitnesses (roots : Array Expr) (products : NativeTypeGraph.ModuleProducts)
    (io : Bool := false) : MetaM Json := do
  let observation ← observeTypes roots products
  let graph ← jsonValue (observation.getObjVal? "typeGraph")
  let witnesses ← runtimeWitnesses graph io
  let document := (observation.setObjVal! "schema" (toJson "lean-jvm-private-nominal-observations/2")).setObjVal!
    "runtimeWitnesses" witnesses
  unless document.compress.utf8ByteSize ≤ 4194304 do
    throwError "NominalWitness: encoded observation byte budget"
  return document

private def scalarLane (type : IR.IRType) : Bool :=
  [IR.IRType.uint8, .uint16, .uint32, .uint64, .usize, .float, .float32].contains type

private structure Emitted where
  row : Json
  raw : IR.Decl
  callable : IR.Decl
  owner : Name

private def emit (env : Environment) (selected : Selected)
    (rootTypes : Array Expr) : MetaM Emitted := do
  let mut arguments := #[]
  let mut expectedArgs := #[]
  for type in selected.signature.arguments do
    let index ← rootIndex rootTypes type
    arguments := arguments.push (toJson index)
    expectedArgs := expectedArgs.push rootTypes[index]!
  let resultIndex ← rootIndex rootTypes selected.signature.result
  let result := rootTypes[resultIndex]!
  let expectedResult := if selected.signature.io then mkApp (mkConst ``IO) result else result
  let expected := expectedArgs.foldr (fun arg body => mkForall .anonymous .default arg body) expectedResult
  unless ← Meta.withTransparency .default (Meta.isDefEq selected.actual expected) do
    throwError "NominalEntry: actual/expected native signature mismatch"
  let some raw := NativeEntryTransport.findInterpreterDecl env selected.name
    | throwError "NominalEntry: original raw interpreter declaration absent"
  unless raw.name == selected.name && !raw.isExtern && raw.getInfo.sorryDep?.isNone do
    throwError "NominalEntry: raw declaration identity/safety refusal"
  let boxed := if raw.params.isEmpty then none else NativeEntryTransport.findInterpreterDeclBoxed env selected.name
  let callable := boxed.getD raw
  let runtimeArity := selected.signature.arguments.size + (if selected.signature.io then 1 else 0)
  let resultIR ← NativeTypeGraph.observeIRType result
  let nullaryScalar := !selected.signature.io && selected.signature.arguments.isEmpty &&
    scalarLane resultIR && callable.resultType == resultIR
  unless !callable.isExtern && callable.getInfo.sorryDep?.isNone && callable.params.size == runtimeArity &&
      callable.params.all (fun p => !p.borrow && NativeEntryTransport.boxedLane p.ty) &&
      (NativeEntryTransport.boxedLane callable.resultType || nullaryScalar) do
    throwError "NominalEntry: unsupported owned callable ABI"
  discard <| jsonValue (NativeEntryTransport.checkDecl raw)
  discard <| jsonValue (NativeEntryTransport.checkDecl callable)
  let some owner := NativeEntryTransport.origin env selected.name
    | throwError "NominalEntry: entry lacks compiled module origin"
  let signature := Json.mkObj [("arguments", Json.arr arguments), ("result", toJson resultIndex),
    ("effect", toJson (if selected.signature.io then "io" else "pure"))]
  let argumentPlan := selected.signature.arguments.mapIdx fun index _ =>
    Json.mkObj [("kind", toJson "argument"), ("index", toJson index)]
  let argumentPlan := argumentPlan ++ (if selected.signature.io then #[Json.mkObj [
    ("kind", toJson "io-world"), ("representation", toJson "canonical-erased-zero")]] else #[])
  let resultABI := if nullaryScalar then Json.mkObj [("kind", toJson "raw-nullary-scalar"),
      ("lane", toJson resultIR), ("resultRoot", toJson resultIndex)]
    else Json.mkObj [("kind", toJson "boxed-object-lane")]
  let row := Json.mkObj [("name", NativeEntryTransport.nameJson selected.name),
    ("kind", toJson selected.kind), ("levelParams", Json.arr #[]),
    ("compiledModule", NativeEntryTransport.nameJson owner), ("actualType", ← encode selected.actual),
    ("typeCheck", Json.mkObj [("algorithm", toJson "Lean.Meta.isDefEq"),
      ("transparency", toJson "default"), ("signature", signature), ("expectedType", ← encode expected)]),
    ("semanticArity", toJson selected.signature.arguments.size), ("runtimeArity", toJson runtimeArity),
    ("argumentPlan", Json.arr argumentPlan), ("resultABI", resultABI),
    ("raw", NativeEntryTransport.abiJson raw), ("callable", NativeEntryTransport.abiJson callable),
    ("selection", toJson (if boxed.isSome then "original-interpreter-boxed-lookup" else "original-owned-raw"))]
  return { row, raw, callable, owner }

private def runMeta {α} (env : Environment) (action : MetaM α) : IO α := do
  let (value, _, _) ← action.toIO
    { fileName := "<native-v3-candidate>", fileMap := default,
      maxRecDepth := 256, maxHeartbeats := 200000 } { env }
  return value

private def selectedRoots (selected : Array Selected) : MetaM (Array Expr) := do
  let mut roots := #[]
  let mut exact : Std.HashSet Expr := {}
  for entry in selected do
    for type in entry.signature.arguments.push entry.signature.result do
      unless !type.hasMVar && !type.hasFVar && !type.hasLevelParam && !type.hasLooseBVars do
        throwError "NominalEntry: open/dependent catalog type"
      let type ← Meta.withTransparency .default (Meta.whnf type)
      if exact.contains type then continue
      exact := exact.insert type
      let mut found := false
      for old in roots do
        if ← Meta.withTransparency .default (Meta.isDefEq old type) then
          found := true
          break
      unless found do
        unless roots.size < 1024 do throwError "NominalEntry: distinct catalog root limit"
        roots := roots.push type
  return roots

private def keys! (j : Json) (expected : List String) : IO Unit := do
  let fields ← NativeEntryTransport.checkedIO j.getObj?
  unless fields.size == expected.length do throw <| IO.userError "NominalEntry: unknown/missing fields"
  for key in expected do discard <| NativeEntryTransport.checkedIO (j.getObjVal? key)

private def digest! (s : String) : IO Unit :=
  unless s.length == 64 && s.toList.all (fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) do
    throw <| IO.userError "NominalEntry: malformed SHA-256"

private def requestNames (request : Json) (origins : Bool := false) : IO (Name × Array Name) := do
  keys! request (if origins then ["schema", "module", "entries"]
    else ["schema", "module", "entries", "moduleProductsSHA256"])
  let schema ← NativeEntryTransport.checkedIO (request.getObjValAs? String "schema")
  unless schema == (if origins then "lean-native-entry-origin-requests/1" else "lean-native-entry-requests/3") do
    throw <| IO.userError "NominalEntry: request schema"
  unless origins do digest! (← NativeEntryTransport.checkedIO (request.getObjValAs? String "moduleProductsSHA256"))
  let module ← NativeEntryTransport.checkedIO <| NativeEntryTransport.checkedName
    (← NativeEntryTransport.checkedIO (request.getObjVal? "module"))
  unless !module.isAnonymous do throw <| IO.userError "NominalEntry: anonymous module"
  let entries ← NativeEntryTransport.checkedIO (request.getObjValAs? (Array Json) "entries")
  unless entries.size > 0 && entries.size ≤ 1024 do throw <| IO.userError "NominalEntry: entry count"
  let mut names := #[]
  for entry in entries do
    keys! entry ["name"]
    let name ← NativeEntryTransport.checkedIO <| NativeEntryTransport.checkedName
      (← NativeEntryTransport.checkedIO (entry.getObjVal? "name"))
    unless !names.contains name do throw <| IO.userError "NominalEntry: duplicate entry"
    names := names.push name
  return (module, names)

private def moduleProducts (document : Json) : IO (NativeTypeGraph.ModuleProducts × Array Name) := do
  keys! document ["schema", "modules"]
  unless (← NativeEntryTransport.checkedIO (document.getObjValAs? String "schema")) ==
      "lean-jvm-used-module-products/1" do throw <| IO.userError "NominalEntry: product schema"
  let rows ← NativeEntryTransport.checkedIO (document.getObjValAs? (Array Json) "modules")
  unless rows.size ≤ 256 do throw <| IO.userError "NominalEntry: product count"
  let roles := #[".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"]
  let mut products : NameMap String := {}
  let mut names := #[]
  let mut total := 0
  for row in rows do
    keys! row ["module", "productSha256", "products"]
    let name ← NativeEntryTransport.checkedIO <| NativeEntryTransport.checkedName
      (← NativeEntryTransport.checkedIO (row.getObjVal? "module"))
    unless !name.isAnonymous && (products.find? name).isNone do
      throw <| IO.userError "NominalEntry: duplicate/anonymous product module"
    let primary ← NativeEntryTransport.checkedIO (row.getObjValAs? String "productSha256")
    digest! primary
    let ps ← NativeEntryTransport.checkedIO (row.getObjValAs? (Array Json) "products")
    unless ps.size == roles.size do throw <| IO.userError "NominalEntry: missing product roles"
    for i in [:ps.size] do
      let p := ps[i]!
      let present ← NativeEntryTransport.checkedIO (p.getObjValAs? Bool "present")
      keys! p (if present then ["role", "present", "bytes", "sha256"] else ["role", "present"])
      unless (← NativeEntryTransport.checkedIO (p.getObjValAs? String "role")) == roles[i]! do
        throw <| IO.userError "NominalEntry: product role order"
      if present then
        let bytes ← NativeEntryTransport.checkedIO (p.getObjValAs? Nat "bytes")
        let sha ← NativeEntryTransport.checkedIO (p.getObjValAs? String "sha256")
        digest! sha
        total := total + bytes
        unless bytes ≤ 67108864 && total ≤ 268435456 do throw <| IO.userError "NominalEntry: product byte budget"
        if i == 0 && sha != primary then throw <| IO.userError "NominalEntry: primary product mismatch"
      else if i == 0 then throw <| IO.userError "NominalEntry: primary product absent"
    names := names.push name
    products := products.insert name primary
  return ((fun name => products.find? name), names)

/-- Complete advisory entry-origin inventory. Not entry evidence and no hashes. -/
def inventorySelected (env : Environment) (request : Json) : IO Json := do
  let (module, names) ← requestNames request true
  unless (env.getModuleIdx? module).isSome do throw <| IO.userError "NominalEntry: compiled root absent"
  runMeta env do
    let selected ← names.mapM (select env)
    let roots ← selectedRoots selected
    let inventory ← NativeTypeGraph.inventoryOrigins roots
    return Json.mkObj [("schema", toJson "lean-native-entry-origin-inventory/1"),
      ("scope", toJson "advisory-no-entry-authority"), ("request", request), ("types", inventory)]

/-- Actual native entry observations. Callers must still establish issuer byte
    custody, source IR reconciliation and cohort admission independently. -/
def inspectEntries (env : Environment) (request productsDocument : Json) : IO Json := do
  let (module, names) ← requestNames request
  unless (env.getModuleIdx? module).isSome && env.header.moduleNames.size ≤ 4096 do
    throw <| IO.userError "NominalEntry: compiled root/import count"
  let (products, productNames) ← moduleProducts productsDocument
  let (discovery, rootTypes, emitted, witnesses) ← runMeta env do
    let selected ← names.mapM (select env)
    let roots ← selectedRoots selected
    let discovery ← NativeTypeGraph.discover roots products
    let descriptors ← jsonValue (discovery.logical.getObjValAs? (Array Json) "roots")
    let rootTypes ← descriptors.mapM (reconstruct discovery.logical ·)
    unless rootTypes.size == discovery.canonicalRoots.size do throwError "NominalEntry: root catalog size"
    for i in [:rootTypes.size] do
      unless ← Meta.withTransparency .default (Meta.isDefEq rootTypes[i]! discovery.canonicalRoots[i]!) do
        throwError "NominalEntry: canonical root native DefEq mismatch"
    let emitted ← selected.mapM (fun entry => emit env entry rootTypes)
    let witnesses ← runtimeWitnesses discovery.logical (selected.any (·.signature.io))
    return (discovery, rootTypes, emitted, witnesses)
  let definitions ← NativeEntryTransport.checkedIO (discovery.logical.getObjValAs? (Array Json) "definitions")
  let mut used : Array Name := #[]
  for d in definitions do
    let o ← NativeEntryTransport.checkedIO (d.getObjVal? "origin")
    let name ← NativeEntryTransport.checkedIO <| NativeEntryTransport.checkedName
      (← NativeEntryTransport.checkedIO (o.getObjVal? "module"))
    unless used.contains name do used := used.push name
  unless used.size == productNames.size && used.all productNames.contains do
    throw <| IO.userError "NominalEntry: product/inventory set mismatch"
  let mut roots := #[]
  let mut origins : NameMap Name := {}
  let mut forced : NameMap IR.Decl := {}
  for e in emitted do
    roots := roots ++ #[e.raw.name, e.callable.name]
    origins := origins.insert e.callable.name e.owner
    for d in #[e.raw, e.callable] do
      if let some old := forced.find? d.name then
        unless toJson old == toJson d do throw <| IO.userError "NominalEntry: conflicting lookup-returned declaration"
      forced := forced.insert d.name d
  let (declarations, dynamic) ← NativeEntryTransport.rows env roots origins forced
  let inventory ← NativeEntryTransport.initializerInventory env
  let encodedRoots ← rootTypes.mapM (fun t => NativeEntryTransport.checkedIO (NativeEntryTransport.encodeType t))
  let document := Json.mkObj [("schema", toJson "lean-native-entry-evidence/3"),
    ("producer", toJson "NativeNominalEntryEvidence.exportEntries"),
    ("leanCommit", toJson Lean.githash), ("leanVersion", toJson Lean.versionString),
    ("compiledModule", NativeEntryTransport.nameJson module),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits), ("target", toJson System.Platform.target)]),
    ("request", request), ("moduleProducts", productsDocument),
    ("typeGraph", discovery.logical), ("rootTypes", Json.arr encodedRoots),
    ("representation", discovery.layouts), ("runtimeWitnesses", witnesses),
    ("entries", Json.arr (emitted.map (·.row))), ("declarations", Json.arr declarations),
    ("importedModuleOrder", Json.arr (env.header.moduleNames.map NativeEntryTransport.nameJson)),
    ("initializerAttributeInventory", Json.arr inventory),
    ("initializerAttributeScope", toJson "actual-imported-module-and-IR-entries-not-execution"),
    ("dynamicAPSites", toJson dynamic), ("dynamicClosureProven", toJson false),
    ("initializationPlanScope", toJson "external-source-phase-capture-required"), ("guestKernelAdmission", toJson false)]
  unless document.compress.utf8ByteSize ≤ 16777216 do throw <| IO.userError "NominalEntry: output byte budget"
  return document

/-- Native CLI entry, intentionally not linked/pinned/published in this checkpoint. -/
unsafe def exportEntries (requestPath productsPath : String) : IO Json := do
  let request ← NativeEntryTransport.checkedIO <| Json.parse (← NativeEntryTransport.readBounded requestPath 65536)
  let products ← NativeEntryTransport.checkedIO <| Json.parse (← NativeEntryTransport.readBounded productsPath 4194304)
  let (module, _) ← requestNames request
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module, importAll := true, isMeta := true }] {} (loadExts := true) (level := .private)
  inspectEntries env request products

unsafe def exportOrigins (requestPath : String) : IO Json := do
  let request ← NativeEntryTransport.checkedIO <| Json.parse (← NativeEntryTransport.readBounded requestPath 65536)
  let (module, _) ← requestNames request true
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module, importAll := true, isMeta := true }] {} (loadExts := true) (level := .private)
  inventorySelected env request

end NativeNominalEntryEvidence

unsafe def main (args : List String) : IO Unit := do
  match args with
  | ["--entries", request, "--module-products", products] =>
    IO.println (← NativeNominalEntryEvidence.exportEntries request products).compress
  | ["--entry-origins", request] => IO.println (← NativeNominalEntryEvidence.exportOrigins request).compress
  | _ => throw <| IO.userError "usage: --entry-origins REQUEST.json | --entries REQUEST.json --module-products PRODUCTS.json"
