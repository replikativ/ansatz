import Lean

/-!
Opt-in general entry evidence v2, with frozen v1 transport lineage from
NativeEntryEvidence.lean (e89beefe6ebb864d830367a377360d68cbce89c97fa6a5a5e9dab8877b6c6629).
This executable never evaluates an entry and does not confer Java kernel
admission. The accepted v1 source and binary are unchanged.
-/
open Lean

namespace NativeGeneralEntryEvidence

private def nameJson : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", nameJson p, toJson s]
  | .num p n => Json.arr #[toJson "num", nameJson p, toJson (toString n)]
local instance : ToJson Name := ⟨nameJson⟩

private structure Budget where
  nodes : Nat := 0
  characters : Nat := 0
private abbrev EncodeM := StateT Budget (Except String)
private def tick (characters : Nat := 0) : EncodeM Unit := do
  let b ← get
  unless b.nodes < 8192 && b.characters + characters ≤ 131072 do
    throw "entry type/IR metadata exceeds node/text budget"
  set ({ nodes := b.nodes + 1, characters := b.characters + characters } : Budget)
private def depth! (depth : Nat) : EncodeM Unit := do
  unless depth < 128 do throw "entry type/Name exceeds depth budget"
private partial def checkName (n : Name) (depth : Nat := 0) : EncodeM Unit := do
  depth! depth
  tick
  match n with
  | .anonymous => pure ()
  | .str p s => tick s.utf8ByteSize; checkName p (depth + 1)
  | .num p v =>
    unless v ≤ 18446744073709551615 do throw "Name numeric component exceeds UInt64"
    checkName p (depth + 1)
private partial def levelJson (u : Level) (depth : Nat) : EncodeM Json := do
  unless depth < 256 do throw "entry universe AST exceeds depth budget"
  tick
  match u with
  | .zero => return Json.arr #[toJson "zero"]
  | .succ p => return Json.arr #[toJson "succ", ← levelJson p (depth + 1)]
  | .max a b => return Json.arr #[toJson "max", ← levelJson a (depth + 1), ← levelJson b (depth + 1)]
  | .imax a b => return Json.arr #[toJson "imax", ← levelJson a (depth + 1), ← levelJson b (depth + 1)]
  | .param n => checkName n; return Json.arr #[toJson "param", nameJson n]
  | .mvar _ => throw "unresolved universe metavariable"
private def binderJson : BinderInfo → Json
  | .default => toJson "default"
  | .implicit => toJson "implicit"
  | .strictImplicit => toJson "strictImplicit"
  | .instImplicit => toJson "instImplicit"
private def dataJson (v : DataValue) : EncodeM Json := do
  tick
  match v with
  | .ofString s => tick s.utf8ByteSize; return Json.arr #[toJson "string", toJson s]
  | .ofBool b => return Json.arr #[toJson "bool", toJson b]
  | .ofName n => checkName n; return Json.arr #[toJson "name", nameJson n]
  | .ofNat n => let s := toString n; tick s.utf8ByteSize; return Json.arr #[toJson "nat", toJson s]
  | .ofInt n => let s := toString n; tick s.utf8ByteSize; return Json.arr #[toJson "int", toJson s]
  | .ofSyntax _ => throw "syntax-valued type metadata is outside entry evidence v1"
private partial def exprJson (e : Expr) (depth : Nat := 0) : EncodeM Json := do
  unless depth < 256 do throw "entry type AST exceeds depth budget"
  tick
  match e with
  | .bvar i => return Json.arr #[toJson "bvar", toJson i]
  | .fvar _ | .mvar _ => throw "open or unresolved entry type"
  | .sort u => return Json.arr #[toJson "sort", ← levelJson u (depth + 1)]
  | .const n us =>
    checkName n
    unless us.length ≤ 128 do throw "universe argument bound"
    return Json.arr #[toJson "const", nameJson n, Json.arr (← us.toArray.mapM (levelJson · (depth + 1)))]
  | .app f a => return Json.arr #[toJson "app", ← exprJson f (depth + 1), ← exprJson a (depth + 1)]
  | .lam n t b bi =>
    checkName n
    return Json.arr #[toJson "lam", nameJson n, binderJson bi, ← exprJson t (depth + 1), ← exprJson b (depth + 1)]
  | .forallE n t b bi =>
    checkName n
    return Json.arr #[toJson "forall", nameJson n, binderJson bi, ← exprJson t (depth + 1), ← exprJson b (depth + 1)]
  | .letE n t v b nondep =>
    checkName n
    return Json.arr #[toJson "let", nameJson n, toJson nondep, ← exprJson t (depth + 1),
      ← exprJson v (depth + 1), ← exprJson b (depth + 1)]
  | .lit (.natVal n) =>
    let s := toString n
    tick s.utf8ByteSize
    return Json.arr #[toJson "nat", toJson s]
  | .lit (.strVal s) => tick s.utf8ByteSize; return Json.arr #[toJson "string", toJson s]
  | .mdata md b =>
    let entries := md.entries.take 129
    unless entries.length ≤ 128 do throw "type metadata entry bound"
    let entries ← entries.toArray.mapM fun (n, v) => do
      checkName n
      return Json.arr #[nameJson n, ← dataJson v]
    return Json.arr #[toJson "mdata", Json.arr entries, ← exprJson b (depth + 1)]
  | .proj n i b =>
    checkName n
    return Json.arr #[toJson "proj", nameJson n, toJson i, ← exprJson b (depth + 1)]
private def encodeType (e : Expr) : Except String Json := do
  let (j, _) ← (exprJson e).run {}
  return j
private partial def decodeName (j : Json) (depth : Nat) : Except String Name := do
  unless depth < 128 do throw "requested Name depth bound"
  let a ← j.getArr?
  if a == #[toJson "anonymous"] then return .anonymous
  unless a.size == 3 do throw "malformed requested typed Name"
  let kind ← a[0]!.getStr?
  let p ← decodeName a[1]! (depth + 1)
  let leaf ← a[2]!.getStr?
  unless leaf.utf8ByteSize ≤ 4096 do throw "requested Name text bound"
  if kind == "str" then return .str p leaf
  unless kind == "num" && leaf.utf8ByteSize ≤ 20 do throw "malformed numeric Name component"
  let some n := leaf.toNat? | throw "invalid numeric Name component"
  unless toString n == leaf && n ≤ 18446744073709551615 do throw "noncanonical/out-of-range numeric Name"
  return .num p n
private def checkedName (j : Json) : Except String Name := do
  let n ← decodeName j 0
  let (_, _) ← (checkName n).run {}
  return n

private def checkedIO {α} (v : Except String α) : IO α :=
  match v with
  | .ok a => pure a
  | .error message => throw <| IO.userError message
private def readBounded (path : String) (limit : Nat) : IO String :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    repeat
      let chunk ← handle.read 4096
      if chunk.isEmpty then break
      unless bytes.size + chunk.size ≤ limit do throw <| IO.userError "input byte bound exceeded"
      bytes := bytes ++ chunk
    let some text := String.fromUTF8? bytes | throw <| IO.userError "input is not exact UTF-8"
    return text
private inductive ValueType where
  | nat | int | bool | string | unit | char | bytes
  | machineInt (bits : Nat) (signed : Bool)
  | word (signed : Bool)
  | float (bits : Nat)
  | product (first second : ValueType)
  | option (element : ValueType)
  | list (element : ValueType)
  | array (element : ValueType)
  | sum (left right : ValueType)
  | except (error value : ValueType)
  deriving Inhabited

private partial def valueTypeJson : ValueType → Json
  | .nat => Json.mkObj [("kind", toJson "nat")]
  | .int => Json.mkObj [("kind", toJson "int")]
  | .bool => Json.mkObj [("kind", toJson "bool")]
  | .string => Json.mkObj [("kind", toJson "string")]
  | .unit => Json.mkObj [("kind", toJson "unit")]
  | .char => Json.mkObj [("kind", toJson "char")]
  | .bytes => Json.mkObj [("kind", toJson "bytes")]
  | .machineInt bits signed => Json.mkObj [("kind", toJson "machine-int"), ("bits", toJson bits), ("signed", toJson signed)]
  | .word signed => Json.mkObj [("kind", toJson "word"), ("signed", toJson signed)]
  | .float bits => Json.mkObj [("kind", toJson "float"), ("bits", toJson bits) ]
  | .product first second => Json.mkObj [("kind", toJson "product"),
      ("first", valueTypeJson first), ("second", valueTypeJson second)]
  | .option element => Json.mkObj [("kind", toJson "option"), ("element", valueTypeJson element)]
  | .list element => Json.mkObj [("kind", toJson "list"), ("element", valueTypeJson element)]
  | .array element => Json.mkObj [("kind", toJson "array"), ("element", valueTypeJson element)]
  | .sum left right => Json.mkObj [("kind", toJson "sum"), ("left", valueTypeJson left), ("right", valueTypeJson right)]
  | .except error value => Json.mkObj [("kind", toJson "except"), ("error", valueTypeJson error), ("value", valueTypeJson value)]

private def machineIntName (bits : Nat) (signed : Bool) : Name :=
  if signed then
    if bits == 8 then ``Int8 else if bits == 16 then ``Int16 else if bits == 32 then ``Int32 else ``Int64
  else
    if bits == 8 then ``UInt8 else if bits == 16 then ``UInt16 else if bits == 32 then ``UInt32 else ``UInt64

private partial def valueTypeExpr : ValueType → Expr
  | .nat => mkConst ``Nat
  | .int => mkConst ``Int
  | .bool => mkConst ``Bool
  | .string => mkConst ``String
  | .unit => mkConst ``Unit
  | .char => mkConst ``Char
  | .bytes => mkConst ``ByteArray
  | .machineInt bits signed => mkConst (machineIntName bits signed)
  | .word signed => mkConst (if signed then ``ISize else ``USize)
  | .float bits => mkConst (if bits == 32 then ``Float32 else ``Float)
  | .product first second => mkApp2 (mkConst ``Prod [.zero, .zero]) (valueTypeExpr first) (valueTypeExpr second)
  | .option element => mkApp (mkConst ``Option [.zero]) (valueTypeExpr element)
  | .list element => mkApp (mkConst ``List [.zero]) (valueTypeExpr element)
  | .array element => mkApp (mkConst ``Array [.zero]) (valueTypeExpr element)
  | .sum left right => mkApp2 (mkConst ``Sum [.zero, .zero]) (valueTypeExpr left) (valueTypeExpr right)
  | .except error value => mkApp2 (mkConst ``Except [.zero, .zero]) (valueTypeExpr error) (valueTypeExpr value)

private structure Signature where
  arguments : Array ValueType
  result : ValueType
  io : Bool
  deriving Inhabited

private def signatureJson (signature : Signature) : Json :=
  Json.mkObj [("arguments", Json.arr (signature.arguments.map valueTypeJson)),
    ("result", valueTypeJson signature.result), ("effect", toJson (if signature.io then "io" else "pure"))]

private def signatureExpr (signature : Signature) : Expr :=
  let result := valueTypeExpr signature.result
  let result := if signature.io then mkApp (mkConst ``IO) result else result
  signature.arguments.foldr (fun argument body => .forallE .anonymous (valueTypeExpr argument) body .default) result

/-- Normalize only in the actual native Meta context. No erased IR type is used
    to infer a source type, and no unknown head is classified by its spelling. -/
private partial def inferValueType (type : Expr) (depth remaining : Nat) : MetaM (ValueType × Nat) := do
  unless depth < 32 && remaining > 0 do throwError "SignatureLimit: type depth/node budget exceeded"
  let type ← Meta.withTransparency .default (Meta.whnf type)
  unless !type.hasMVar && !type.hasFVar && !type.hasLevelParam && !type.hasLooseBVars do
    throwError "UnsupportedDependentType: value type is open or depends on an earlier argument"
  if ← Meta.isProp type then throwError "UnsupportedProofType: proofs are not host values"
  let remaining := remaining - 1
  for (name, result) in #[( ``Nat, ValueType.nat), (``Int, .int), (``Bool, .bool),
                         (``String, .string), (``Unit, .unit), (``Char, .char), (``ByteArray, .bytes),
                         (``UInt8, .machineInt 8 false), (``UInt16, .machineInt 16 false),
                         (``UInt32, .machineInt 32 false), (``UInt64, .machineInt 64 false),
                         (``Int8, .machineInt 8 true), (``Int16, .machineInt 16 true),
                         (``Int32, .machineInt 32 true), (``Int64, .machineInt 64 true),
                         (``USize, .word false), (``ISize, .word true),
                         (``Float, .float 64), (``Float32, .float 32)] do
    if ← Meta.withTransparency .default (Meta.isDefEq type (mkConst name)) then return (result, remaining)
  match type with
  | .sort _ => throwError "UnsupportedTypeFormer: universe/type arguments are not host values"
  | .forallE .. => throwError "UnsupportedHigherOrderType: function-valued data is not supported"
  | _ => pure ()
  let head := type.getAppFn
  let arguments := type.getAppArgs
  if head.isConstOf ``Prod && arguments.size == 2 then
    let (first, remaining) ← inferValueType arguments[0]! (depth + 1) remaining
    let (second, remaining) ← inferValueType arguments[1]! (depth + 1) remaining
    return (.product first second, remaining)
  if head.isConstOf ``Option && arguments.size == 1 then
    let (element, remaining) ← inferValueType arguments[0]! (depth + 1) remaining
    return (.option element, remaining)
  if head.isConstOf ``List && arguments.size == 1 then
    let (element, remaining) ← inferValueType arguments[0]! (depth + 1) remaining
    return (.list element, remaining)
  if head.isConstOf ``Array && arguments.size == 1 then
    let (element, remaining) ← inferValueType arguments[0]! (depth + 1) remaining
    return (.array element, remaining)
  for (name, isExcept) in #[( ``Sum, false), (``Except, true)] do
    if head.isConstOf name && arguments.size == 2 then
      let (left, remaining) ← inferValueType arguments[0]! (depth + 1) remaining
      let (right, remaining) ← inferValueType arguments[1]! (depth + 1) remaining
      return (if isExcept then .except left right else .sum left right, remaining)
  throwError "UnsupportedValueType: no descriptor for this actual native type"

/-- This probe must run BEFORE reducing a Pi telescope: IO unfolds to an internal
    world function. Its world is never a public user argument. The source type is
    closed, so only the fresh candidate payload can be assigned by this probe. -/
private def ioPayload? (type : Expr) : MetaM (Option Expr) := do
  let payload ← Meta.mkFreshExprMVar (some (mkSort (.succ .zero)))
  let expected := mkApp (mkConst ``IO) payload
  if ← Meta.withTransparency .default (Meta.isDefEq type expected) then
    let payload ← instantiateMVars payload
    unless !payload.hasMVar && !payload.hasFVar && !payload.hasLevelParam && !payload.hasLooseBVars do
      throwError "UnsupportedDependentIO: IO payload is not a closed monomorphic value type"
    return some payload
  return none

private partial def inferSignature (type : Expr) (arguments : Array ValueType := #[])
    (remaining : Nat := 512) : MetaM Signature := do
  if let some payload ← ioPayload? type then
    let (result, _) ← inferValueType payload 0 remaining
    return { arguments, result, io := true }
  let type ← Meta.withTransparency .default (Meta.whnf type)
  match type with
  | .forallE name domain body bi =>
    unless bi == .default do throwError "UnsupportedBinder: implicit and instance parameters are not admitted"
    unless arguments.size < 64 do throwError "SignatureLimit: more than 64 explicit value arguments"
    let (argument, remaining) ← inferValueType domain 0 remaining
    Meta.withLocalDecl name bi domain fun argumentValue =>
      inferSignature (body.instantiate1 argumentValue) (arguments.push argument) remaining
  | _ =>
    let (result, _) ← inferValueType type 0 remaining
    return { arguments, result, io := false }

private def checkType (ci : ConstantInfo) : MetaM (Signature × Expr × Expr) := do
  unless ← Compiler.LCNF.declIsNotUnsafe ci.name do
    throwError "UnsupportedEntrySafety: entry is unsafe or partial"
  let signature ← inferSignature ci.type
  let expected := signatureExpr signature
  unless ← Meta.withTransparency .default (Meta.isDefEq ci.type expected) do
    throwError "SignatureMismatch: native inferred descriptor does not match the actual constant type"
  let actual ← instantiateMVars ci.type
  let expected ← instantiateMVars expected
  unless !actual.hasMVar && !actual.hasFVar && !actual.hasLevelParam && !actual.hasLooseBVars &&
      !expected.hasMVar && !expected.hasFVar && !expected.hasLevelParam && !expected.hasLooseBVars do
    throwError "UnsupportedOpenType: type remains open after native DefEq"
  return (signature, actual, expected)

-- Actual pinned original interpreter lookup, including base-module-index boxed
-- lookup. Do not replace this with mkBoxedName or a display/suffix heuristic.
@[extern "lean_ir_find_env_decl"]
private opaque findInterpreterDecl (env : Environment) (name : Name) : Option IR.Decl
@[extern "lean_ir_find_env_decl_boxed"]
private opaque findInterpreterDeclBoxed (env : Environment) (name : Name) : Option IR.Decl

private def boxedLane : IR.IRType → Bool
  | .object | .tobject | .tagged => true
  | _ => false
private def origin (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

-- The existing structural IR transport, copied byte-for-byte in shape from
-- Export.lean so consumers can compare actual declarations rather than pretty text.
deriving instance ToJson for IR.VarId, IR.JoinPointId, IR.IRType, IR.Arg, IR.LitVal,
  IR.CtorInfo, IR.Expr, IR.Param, IR.DeclInfo, ExternEntry, ExternAttrData
private def node (op : String) (args : Array Json) : Json := Json.arr (#[toJson op] ++ args)
mutual
private partial def bodyJson : IR.FnBody → Json
  | .vdecl x t e b => node "vdecl" #[toJson x, toJson t, toJson e, bodyJson b]
  | .jdecl j xs v b => node "jdecl" #[toJson j, toJson xs, bodyJson v, bodyJson b]
  | .set x i y b => node "set" #[toJson x, toJson i, toJson y, bodyJson b]
  | .setTag x i b => node "setTag" #[toJson x, toJson i, bodyJson b]
  | .uset x i y b => node "uset" #[toJson x, toJson i, toJson y, bodyJson b]
  | .sset x i o y t b => node "sset" #[toJson x, toJson i, toJson o, toJson y, toJson t, bodyJson b]
  | .inc x n c p b => node "inc" #[toJson x, toJson n, toJson c, toJson p, bodyJson b]
  | .dec x n c p b => node "dec" #[toJson x, toJson n, toJson c, toJson p, bodyJson b]
  | .del x b => node "del" #[toJson x, bodyJson b]
  | .case t x ty cs => node "case" #[nameJson t, toJson x, toJson ty, Json.arr (cs.map altJson)]
  | .ret x => node "ret" #[toJson x]
  | .jmp j ys => node "jmp" #[toJson j, toJson ys]
  | .unreachable => node "unreachable" #[]
private partial def altJson : IR.Alt → Json
  | .ctor i b => node "ctor" #[toJson i, bodyJson b]
  | .default b => node "default" #[bodyJson b]
end
local instance : ToJson IR.FnBody := ⟨bodyJson⟩
deriving instance ToJson for IR.Decl

private def abiJson (d : IR.Decl) : Json :=
  Json.mkObj [("name", nameJson d.name), ("xs", toJson d.params), ("type", toJson d.resultType)]

/-- Native compiler layout facts, not host-created constructor recipes.
    Generic container input allocation is a separate engine ownership gate. -/
private def fieldLayoutJson : Compiler.LCNF.CtorFieldInfo → Json
  | .erased => Json.mkObj [("kind", toJson "erased")]
  | .void => Json.mkObj [("kind", toJson "void")]
  | .object index type => Json.mkObj [("kind", toJson "object"), ("index", toJson index),
      ("irType", toJson (IR.toIRType type))]
  | .usize index => Json.mkObj [("kind", toJson "usize"), ("index", toJson index)]
  | .scalar bytes offset type => Json.mkObj [("kind", toJson "scalar"),
      ("bytes", toJson bytes), ("offset", toJson offset), ("irType", toJson (IR.toIRType type))]

private def constructorLayout (name : Name) : MetaM Json := do
  let layout ← Compiler.LCNF.getCtorLayout name
  let info := layout.ctorInfo
  let info := Json.mkObj [("name", nameJson info.name), ("cidx", toJson info.cidx),
    ("size", toJson info.size), ("usize", toJson info.usize), ("ssize", toJson info.ssize)]
  return Json.mkObj [("constructor", nameJson name), ("ctorInfo", info),
    ("fields", Json.arr (layout.fieldInfo.map fieldLayoutJson))]

private partial def containerNames (type : ValueType) : Array Name :=
  match type with
  | .product first second => #[``Prod] ++ containerNames first ++ containerNames second
  | .option element => #[``Option] ++ containerNames element
  | .list element => #[``List] ++ containerNames element
  | .array element => containerNames element
  | .sum left right => #[``Sum] ++ containerNames left ++ containerNames right
  | .except error value => #[``Except] ++ containerNames error ++ containerNames value
  | _ => #[]

private def familyLayout (name : Name) : MetaM Json := do
  let some (.inductInfo info) := (← getEnv).find? name
    | throwError "CodecLayoutUnavailable: actual inductive declaration is absent"
  let impure ← Compiler.LCNF.nameToImpureType name
  let trivial ← Compiler.LCNF.hasTrivialImpureStructure? name
  let trivial := trivial.map fun info => Json.mkObj [("constructor", nameJson info.ctorName),
    ("fieldIndex", toJson info.fieldIdx), ("numParams", toJson info.numParams)]
  let constructors ← info.ctors.toArray.mapM constructorLayout
  return Json.mkObj [("typeName", nameJson name), ("irType", toJson (IR.toIRType impure)),
    ("trivialStructure", toJson trivial), ("constructors", Json.arr constructors)]

private def codecWitnesses (signature : Signature) : MetaM Json := do
  let names := signature.arguments.foldl (fun names argument => names ++ containerNames argument)
    (containerNames signature.result)
  let names := if signature.io then names.push ``EST.Out else names
  let mut seen : NameSet := {}
  let mut layouts := #[]
  for name in names do
    if seen.contains name then continue
    seen := seen.insert name
    layouts := layouts.push (← familyLayout name)
  return Json.mkObj [("algorithm", toJson "Lean.Compiler.LCNF.getCtorLayout"),
    ("scope", toJson "actual-persisted-native-compiler-layout-not-host-allocation-authority"),
    ("families", Json.arr layouts)]

/-- Observe special value representations through the actual pinned compiler
    pipeline. Arrays and bytes are runtime-special values, never constructor
    recipes. Signed wrappers/Char must retain their source descriptor even when
    the compiler erases their wrapper into an unsigned scalar lane. -/
private partial def specialTypes (type : ValueType) : Array ValueType :=
  match type with
  | .machineInt .. | .word .. | .float .. | .char | .bytes => #[type]
  | .array element => #[type] ++ specialTypes element
  | .product first second | .sum first second | .except first second => specialTypes first ++ specialTypes second
  | .option element | .list element => specialTypes element
  | _ => #[]

private def nativeRepresentation (signature : Signature) : MetaM Json := do
  let types := signature.arguments.foldl (fun types argument => types ++ specialTypes argument)
    (specialTypes signature.result)
  let mut seen : Array Json := #[]
  let mut observations : Array Json := #[]
  for type in types do
    let descriptor := valueTypeJson type
    if seen.contains descriptor then continue
    seen := seen.push descriptor
    let lcnf ← Compiler.LCNF.toLCNFType (valueTypeExpr type)
    let mono ← Compiler.LCNF.toMonoType lcnf
    let impure ← Compiler.LCNF.toImpureType mono
    observations := observations.push <| Json.mkObj [("type", descriptor), ("irType", toJson (IR.toIRType impure))]
  return Json.mkObj [("algorithm", toJson "Lean.Compiler.LCNF.toLCNFType/toMonoType/toImpureType"),
    ("types", Json.arr observations)]

private def scalarResultType? : ValueType → Option IR.IRType
  | .bool => some .uint8
  | .machineInt bits _ => some (if bits == 8 then .uint8 else if bits == 16 then .uint16 else if bits == 32 then .uint32 else .uint64)
  | .word _ => some .usize
  | .float bits => some (if bits == 32 then .float32 else .float)
  | .char => some .uint32
  | _ => none

private partial def checkIRType (t : IR.IRType) (depth : Nat := 0) : EncodeM Unit := do
  depth! depth
  tick
  match t with
  | .struct n ts =>
    if let some n := n then checkName n
    unless ts.size ≤ 1024 do throw "IR struct type extent bound"
    for t in ts do checkIRType t (depth + 1)
  | .union n ts =>
    checkName n
    unless ts.size ≤ 1024 do throw "IR union type extent bound"
    for t in ts do checkIRType t (depth + 1)
  | _ => pure ()
private def checkParams (ps : Array IR.Param) : EncodeM Unit := do
  unless ps.size ≤ 1024 do throw "IR parameter bound"
  for p in ps do checkIRType p.ty
private def checkIRExpr (e : IR.Expr) : EncodeM Unit := do
  tick
  match e with
  | .ctor info args | .reuse _ info _ args =>
    checkName info.name
    unless args.size ≤ 4096 do throw "IR constructor argument bound"
  | .fap n args | .pap n args =>
    checkName n
    unless args.size ≤ 4096 do throw "IR static argument bound"
  | .ap _ args => unless args.size ≤ 4096 do throw "IR dynamic argument bound"
  | .box ty _ => checkIRType ty
  | .lit (.str s) => tick s.utf8ByteSize
  | .lit (.num n) => tick (toString n).utf8ByteSize
  | _ => pure ()
private partial def checkBody (b : IR.FnBody) (depth : Nat := 0) : EncodeM Unit := do
  unless depth < 512 do throw "IR body depth bound"
  tick
  match b with
  | .vdecl _ t e b => checkIRType t; checkIRExpr e; checkBody b (depth + 1)
  | .jdecl _ ps v b => checkParams ps; checkBody v (depth + 1); checkBody b (depth + 1)
  | .case n _ t cs =>
    checkName n
    checkIRType t
    unless cs.size ≤ 1024 do throw "IR alternatives bound"
    for c in cs do
      match c with
      | .ctor info b => checkName info.name; checkBody b (depth + 1)
      | .default b => checkBody b (depth + 1)
  | b => if b.isTerminal then pure () else checkBody b.body (depth + 1)
private def checkDecl (d : IR.Decl) : Except String Unit := do
  let (_, _) ← (do
    checkName d.name
    checkParams d.params
    checkIRType d.resultType
    match d with
    | .fdecl (body := b) .. => checkBody b
    | .extern (ext := ext) .. =>
      let entries := ext.entries.take 17
      unless entries.length ≤ 16 do throw "extern entry bound"
      for e in entries do
        match e with
        | .standard backend symbol => checkName backend; tick symbol.utf8ByteSize
        | .inline backend pattern => checkName backend; tick pattern.utf8ByteSize
        | .adhoc backend => checkName backend
        | .opaque => tick).run {}
  return ()
private def exprDeps : IR.Expr → Array Name
  | .fap n _ | .pap n _ => #[n]
  | _ => #[]
mutual
private partial def bodyDeps : IR.FnBody → Array Name
  | .vdecl _ _ e b => exprDeps e ++ bodyDeps b
  | .jdecl _ _ v b => bodyDeps v ++ bodyDeps b
  | .case _ _ _ cs => cs.foldl (fun ns c => ns ++ altDeps c) #[]
  | b => if b.isTerminal then #[] else bodyDeps b.body
private partial def altDeps : IR.Alt → Array Name
  | .ctor _ b | .default b => bodyDeps b
end
private partial def dynamicSites : IR.FnBody → Nat
  | .vdecl _ _ e b => (if e matches .ap .. then 1 else 0) + dynamicSites b
  | .jdecl _ _ v b => dynamicSites v + dynamicSites b
  | .case _ _ _ cs => cs.foldl (fun n c => n + match c with
      | .ctor _ b | .default b => dynamicSites b) 0
  | b => if b.isTerminal then 0 else dynamicSites b.body

private def exportTargets (env : Environment) : IO (Std.HashMap String Name) := do
  let mut out := {}
  for (n, _) in env.constants.toList do
    if let some exported := getExportNameFor? env n then
      let (_, _) ← checkedIO <| (do checkName n; checkName exported).run {}
      let symbol := exported.toString
      unless symbol.utf8ByteSize ≤ 4096 && out.size < 4096 do throw <| IO.userError "native export metadata bound"
      if let some previous := out[symbol]? then
        unless previous == n do throw <| IO.userError "ambiguous native export symbol"
      out := out.insert symbol n
  return out

private def entry (env : Environment) (request : Json) : IO (Json × Array Name × NameMap Name × NameMap IR.Decl) := do
  let n ← checkedIO <| checkedName (← checkedIO <| request.getObjVal? "name")
  let fields ← checkedIO <| request.getObj?
  unless fields.size == 1 do throw <| IO.userError "UnsupportedRequest: each v2 entry requests only a name"
  let some ci := env.find? n | throw <| IO.userError "requested constant is absent from actual compiled Environment"
  let kind ← match ci with
    | .defnInfo _ => pure "definition"
    | .opaqueInfo _ => pure "opaque"
    | _ => throw <| IO.userError "entry ConstantInfo kind is unsupported"
  unless ci.name == n do throw <| IO.userError "EntryIdentityMismatch: actual ConstantInfo name differs"
  unless ci.levelParams.isEmpty do throw <| IO.userError "UnsupportedPolymorphicEntry: universe parameters are not admitted"
  unless !ci.isUnsafe && !ci.isPartial do throw <| IO.userError "UnsupportedEntrySafety: unsafe or partial entry"
  unless !ci.type.hasMVar && !ci.type.hasFVar && !ci.type.hasLevelParam && !ci.type.hasLooseBVars do
    throw <| IO.userError "UnsupportedOpenType: actual constant type is open"
  unless !isExtern env n && (Compiler.getImplementedBy? env n).isNone && (getInitFnNameFor? env n).isNone &&
      !isIOUnitInitFn env n && !isIOUnitBuiltinInitFn env n do
    throw <| IO.userError "UnsupportedEntryOrigin: extern, redirected or initialized entries require a separate profile"
  let ((signature, actual, expected), _, _) ← (checkType ci).toIO
    { fileName := "<compiled-native-entry>", fileMap := default, maxRecDepth := 256, maxHeartbeats := 200000 } { env }
  let (witnesses, _, _) ← (codecWitnesses signature).toIO
    { fileName := "<compiled-native-codec-layout>", fileMap := default, maxRecDepth := 256, maxHeartbeats := 200000 } { env }
  let (representation, _, _) ← (nativeRepresentation signature).toIO
    { fileName := "<compiled-native-representation>", fileMap := default, maxRecDepth := 256, maxHeartbeats := 200000 } { env }
  let actual ← checkedIO <| encodeType actual
  let expected ← checkedIO <| encodeType expected
  let some raw := findInterpreterDecl env n | throw <| IO.userError "original interpreter raw lookup found no IR"
  unless raw.name == n && !raw.isExtern && raw.getInfo.sorryDep?.isNone do
    throw <| IO.userError "entry raw IR is extern, mismatched or depends on sorry"
  let boxed := if raw.params.isEmpty then none else findInterpreterDeclBoxed env n
  let selected := boxed.getD raw
  let runtimeArity := signature.arguments.size + (if signature.io then 1 else 0)
  let nullaryScalar := !signature.io && signature.arguments.isEmpty &&
    scalarResultType? signature.result == some selected.resultType
  let nullaryBoolScalar := nullaryScalar && (signature.result matches .bool)
  unless !selected.isExtern && selected.params.size == runtimeArity &&
      selected.params.all (fun parameter => !parameter.borrow && boxedLane parameter.ty) &&
      (boxedLane selected.resultType || nullaryScalar) && selected.getInfo.sorryDep?.isNone do
    throw <| IO.userError "UnsupportedCallableABI: actual interpreter callable is not exact owned boxed arity (or supported nullary scalar)"
  checkedIO <| checkDecl raw
  checkedIO <| checkDecl selected
  let some module := origin env n | throw <| IO.userError "entry is not attributed to an actual compiled module"
  let origins := ({} : NameMap Name).insert selected.name module
  let forced := (({} : NameMap IR.Decl).insert n raw).insert selected.name selected
  return (Json.mkObj [
    ("name", nameJson n), ("kind", toJson kind), ("levelParams", toJson ci.levelParams),
    ("compiledModule", nameJson module), ("actualType", actual),
    ("typeCheck", Json.mkObj [("algorithm", toJson "Lean.Meta.isDefEq"),
      ("signature", signatureJson signature), ("transparency", toJson "default"), ("expectedType", expected)]),
    ("semanticArity", toJson signature.arguments.size), ("runtimeArity", toJson runtimeArity),
    ("codecWitnesses", witnesses), ("nativeRepresentation", representation),
    ("argumentPlan", Json.arr ((signature.arguments.mapIdx fun index _ => Json.mkObj [
      ("kind", toJson "argument"), ("index", toJson index)]) ++
      (if signature.io then #[Json.mkObj [("kind", toJson "io-world"), ("representation", toJson "canonical-erased-zero")]] else #[]))),
    ("resultABI", toJson (if nullaryBoolScalar then "raw-nullary-bool-uint8" else if nullaryScalar then "raw-nullary-scalar" else "boxed-object-lane")),
    ("raw", abiJson raw), ("callable", abiJson selected),
    ("selection", toJson (if boxed.isSome then "original-interpreter-boxed-lookup" else "original-owned-raw"))],
    #[n, selected.name], origins, forced)

private def readRequests (path : String) : IO (Name × Array Json) := do
  let contents ← readBounded path 65536
  unless contents.utf8ByteSize ≤ 65536 do throw <| IO.userError "entry request file exceeds 64KiB"
  let document ← checkedIO <| Json.parse contents
  let fields ← checkedIO <| document.getObj?
  unless fields.size == 3 do throw <| IO.userError "UnsupportedRequest: expected only schema, module and entries"
  unless (← checkedIO <| document.getObjValAs? String "schema") == "lean-native-entry-requests/2" do
    throw <| IO.userError "unknown entry request schema"
  let requests ← checkedIO <| (← checkedIO <| document.getObjVal? "entries").getArr?
  unless 1 ≤ requests.size && requests.size ≤ 1024 do throw <| IO.userError "entry request count must be one to 1024"
  let module ← checkedIO <| checkedName (← checkedIO <| document.getObjVal? "module")
  unless !module.isAnonymous do throw <| IO.userError "compiled module must be nonanonymous"
  return (module, requests)

private def rows (env : Environment) (roots : Array Name) (origins : NameMap Name)
    (forced : NameMap IR.Decl) : IO (Array Json × Nat) := do
  let exports ← exportTargets env
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut rows := #[]
  let mut outputBytes := 0
  let mut dynamic := 0
  while !pending.isEmpty do
    unless pending.size ≤ 32768 do throw <| IO.userError "IR pending frontier exceeds bound"
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    unless rows.size < 2048 do throw <| IO.userError "IR closure exceeds 2048 rows"
    -- Preserve the declaration returned by the original BASE-index boxed lookup;
    -- re-looking up its generated Name could choose a different visibility path.
    let some d := forced.find? n <|> findInterpreterDecl env n
      | throw <| IO.userError "actual static IR dependency is missing"
    unless d.name == n && d.getInfo.sorryDep?.isNone do throw <| IO.userError "IR dependency identity or sorry frontier"
    checkedIO <| checkDecl d
    let initializer := getInitFnNameFor? env n
    let role := if initializer.isSome then "initialized" else if isClosedTermName env n then "closed"
      else if Compiler.LCNF.isSimpleGroundDecl env n then "ground" else if d.params.isEmpty then "value" else "ordinary"
    let redirectTarget := match d with
      | .extern _ _ _ ext => do
        let .standard _ symbol ← getExternEntryFor ext `c | none
        let target ← exports[symbol]?
        guard (target != n)
        let targetDecl ← findInterpreterDecl env target
        guard (!targetDecl.isExtern)
        some (target, targetDecl)
      | _ => none
    let redirect : Option (Name × Json) ← match redirectTarget with
      | none => pure none
      | some (target, decl) => do
        checkedIO <| checkDecl decl
        pure <| some (target, Json.mkObj [("name", nameJson target), ("params", toJson decl.params), ("type", toJson decl.resultType)])
    let deps := (match d with | .fdecl (body := b) .. => bodyDeps b | _ => #[]) ++
      initializer.toArray ++ (redirect.map (fun (pair : Name × Json) => pair.1)).toArray
    unless deps.size ≤ 16384 do throw <| IO.userError "IR static dependency edge bound"
    let owner := origins.find? n <|> origin env n
    let (_, _) ← checkedIO <| (do
      for name in initializer.toArray ++ (redirect.map (fun (pair : Name × Json) => pair.1)).toArray ++ owner.toArray do checkName name).run {}
    let row := Json.mkObj [("kind", toJson "decl"), ("name", nameJson n), ("ir", toJson d),
      ("dependencies", toJson deps), ("redirect", toJson (redirect.map (fun (pair : Name × Json) => pair.2))),
      ("sourceLocal", toJson false), ("sourceModule", toJson owner),
      ("runtime", Json.mkObj [("role", toJson role), ("initializer", toJson initializer),
        ("initializationAction", toJson (if isIOUnitBuiltinInitFn env n then some "builtin-io"
          else if isIOUnitInitFn env n then some "io" else none))])]
    outputBytes := outputBytes + row.compress.utf8ByteSize
    unless outputBytes ≤ 16777216 do throw <| IO.userError "IR closure output exceeds 16MiB"
    dynamic := dynamic + match d with | .fdecl (body := b) .. => dynamicSites b | _ => 0
    seen := seen.insert n
    rows := rows.push row
    pending := pending ++ deps
  return (rows, dynamic)

private def initializerInventory (env : Environment) : IO (Array Json) := do
  let mut result := #[]
  let mut count := 0
  for module in env.header.moduleNames, idx in [:env.header.moduleNames.size] do
    let regular := regularInitAttr.ext.getModuleEntries env idx
    let regularIR := regularInitAttr.ext.getModuleIREntries env idx
    let builtin := builtinInitAttr.ext.getModuleEntries env idx
    let builtinIR := builtinInitAttr.ext.getModuleIREntries env idx
    count := count + regular.size + regularIR.size + builtin.size + builtinIR.size
    unless count ≤ 16384 do throw <| IO.userError "initializer inventory extent bound"
    let (_, _) ← checkedIO <| (do
      for (decl, init) in regular ++ regularIR ++ builtin ++ builtinIR do
        checkName decl
        checkName init).run {}
    result := result.push <| Json.mkObj [("module", nameJson module),
      ("regularModuleEntries", toJson regular), ("regularIREntries", toJson regularIR),
      ("builtinModuleEntries", toJson builtin), ("builtinIREntries", toJson builtinIR)]
  return result

unsafe def exportEntries (requestPath : String) : IO Json := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let (module, requests) ← readRequests requestPath
  let env ← importModules #[{ module, importAll := true, isMeta := true }] {} (loadExts := true) (level := .private)
  unless (env.getModuleIdx? module).isSome && env.header.moduleNames.size ≤ 4096 do
    throw <| IO.userError "actual compiled module or imported module extent differs"
  let (_, _) ← checkedIO <| (do for name in env.header.moduleNames do checkName name).run {}
  let mut entries := #[]
  let mut roots := #[]
  let mut origins : NameMap Name := {}
  let mut forced : NameMap IR.Decl := {}
  let mut seen : NameSet := {}
  for request in requests do
    let (e, rs, os, fs) ← entry env request
    let n ← checkedIO <| checkedName (← checkedIO <| e.getObjVal? "name")
    unless !seen.contains n do throw <| IO.userError "duplicate requested constant"
    seen := seen.insert n
    entries := entries.push e
    roots := roots ++ rs
    for (name, owner) in os do origins := origins.insert name owner
    for (name, decl) in fs do
      if let some old := forced.find? name then
        unless toJson old == toJson decl do throw <| IO.userError "conflicting canonical callable declarations"
      forced := forced.insert name decl
  let (declarations, dynamic) ← rows env roots origins forced
  let inventory ← initializerInventory env
  return Json.mkObj [("schema", toJson "lean-native-entry-evidence/2"),
    ("leanCommit", toJson Lean.githash), ("leanVersion", toJson Lean.versionString),
    ("producer", toJson "NativeGeneralEntryEvidence.exportEntries"), ("compiledModule", nameJson module),
    ("importedModuleOrder", toJson env.header.moduleNames),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits), ("target", toJson System.Platform.target)]),
    ("entries", Json.arr entries), ("declarations", Json.arr declarations),
    ("initializerAttributeInventory", Json.arr inventory),
    ("initializerAttributeScope", toJson "actual-imported-module-and-IR-entries-not-execution"),
    ("dynamicAPSites", toJson dynamic), ("dynamicClosureProven", toJson false),
    ("initializationPlanScope", toJson "external-source-phase-capture-required"),
    ("guestKernelAdmission", toJson false)]

def exportHeader (path : String) : IO Json := do
  let contents ← readBounded path 1048576
  unless contents.utf8ByteSize ≤ 1048576 do throw <| IO.userError "header source exceeds 1MiB"
  let input := Parser.mkInputContext contents path (normalizeLineEndings := false)
  let (header, state, messages) ← Parser.parseHeader input
  if messages.hasErrors then throw <| IO.userError "original header parser reported errors"
  let imports := (Elab.HeaderSyntax.imports header).map fun imp => Json.mkObj [
    ("module", nameJson imp.module), ("importAll", toJson imp.importAll),
    ("isExported", toJson imp.isExported), ("isMeta", toJson imp.isMeta)]
  return Json.mkObj [("schema", toJson "lean-project-header/1"),
    ("leanCommit", toJson Lean.githash), ("leanVersion", toJson Lean.versionString),
    ("fileName", toJson path), ("sourceUTF8Bytes", toJson contents.utf8ByteSize),
    ("lineEndingNormalization", toJson "disabled"), ("isModule", toJson (Elab.HeaderSyntax.isModule header)), ("requestedImports", Json.arr imports),
    ("parserEndByte", toJson state.pos.byteIdx)]

end NativeGeneralEntryEvidence

unsafe def main (args : List String) : IO Unit := do
  let result ← match args with
    | ["--header", path] => NativeGeneralEntryEvidence.exportHeader path
    | ["--entries", requests] => NativeGeneralEntryEvidence.exportEntries requests
    | _ => throw <| IO.userError "usage: --header SOURCE | --entries REQUESTS.json"
  let output := result.compress
  unless output.utf8ByteSize ≤ 16777216 do throw <| IO.userError "entry evidence output exceeds 16MiB"
  IO.println output
