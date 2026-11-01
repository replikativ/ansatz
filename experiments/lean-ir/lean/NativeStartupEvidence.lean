import Lean

/-!
Standalone native ordinary-import/header provenance evidence. Native import may
execute native initialization. No Java initializer is executed by this producer.
The accepted NativeEntryEvidence and Export executables remain unchanged.
-/
open Lean
namespace NativeStartupEvidence

-- BEGIN copied entry-core
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
  depth! depth
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
  depth! depth
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
-- END copied entry-core

-- BEGIN copied entry-ir
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

-- END copied entry-ir

-- BEGIN copied entry-rows
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

-- END copied entry-rows

private def phaseJson : IRPhases → Json
  | .runtime => toJson "runtime"
  | .comptime => toJson "comptime"
  | .all => toJson "all"
private def importJson (imp : Import) : Json := Json.mkObj [
  ("module", nameJson imp.module), ("importAll", toJson imp.importAll),
  ("isExported", toJson imp.isExported), ("isMeta", toJson imp.isMeta)]
private def effectiveJson (imp : EffectiveImport) : Json := Json.mkObj [
  ("import", importJson imp.toImport), ("irPhases", phaseJson imp.irPhases),
  ("hasData", toJson imp.hasData)]
/-- Exact pinned regular fallback sequence. This is not whole-list deduplication. -/
def regularSequence (regular regularIR : Array (Name × Name)) : Array (Name × Name) :=
  regular ++ regularIR.filter (!regular.contains ·)
/-- The source phase decision, separate from native availability and execution. -/
def phaseSelected (inServer : Bool) (modulePhase declarationPhase : IRPhases) : Bool :=
  (inServer || modulePhase != .runtime) || declarationPhase != .runtime
private def ciKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
private def closedCI (ci : ConstantInfo) : IO Unit := do
  unless ci.levelParams.isEmpty && !ci.type.hasMVar && !ci.type.hasFVar &&
      !ci.type.hasLevelParam && !ci.type.hasLooseBVars do
    throw <| IO.userError "startup CI type is polymorphic or open"
private def ciJson (ci : ConstantInfo) : IO Json := do
  closedCI ci
  let (_, _) ← checkedIO <| (checkName ci.name).run {}
  return Json.mkObj [("name", nameJson ci.name), ("kind", toJson (ciKind ci)),
    ("levelParams", toJson ci.levelParams), ("isUnsafe", toJson ci.isUnsafe),
    ("isPartial", toJson ci.isPartial), ("type", ← checkedIO <| encodeType ci.type)]
private def actualCI (env : Environment) (n : Name) : IO ConstantInfo := do
  let some ci := env.find? n | throw <| IO.userError "startup CI absent from actual imported Environment"
  unless ci.name == n do throw <| IO.userError "startup CI identity mismatch"
  closedCI ci
  return ci
private def ioTypeProof (env : Environment) (action : ConstantInfo) (payloadType : Expr) : IO Json := do
  let ((actual, expected), _, _) ← (do
    let expected ← Meta.mkAppM ``IO #[payloadType]
    unless ← Meta.withTransparency .default (Meta.isDefEq action.type expected) do
      throwError "actual startup action type does not match IO payload type"
    let actual ← instantiateMVars action.type
    let expected ← instantiateMVars expected
    unless !actual.hasMVar && !expected.hasMVar && !actual.hasFVar && !expected.hasFVar &&
        !actual.hasLevelParam && !expected.hasLevelParam &&
        !actual.hasLooseBVars && !expected.hasLooseBVars do
      throwError "startup type proof remains open"
    pure (actual, expected) : MetaM (Expr × Expr)).toIO
      { fileName := "<native-startup-type>", fileMap := default,
        maxRecDepth := 256, maxHeartbeats := 200000 } { env }
  return Json.mkObj [("algorithm", toJson "Lean.Meta.isDefEq"),
    ("transparency", toJson "default"), ("actualType", ← checkedIO <| encodeType actual),
    ("expectedType", ← checkedIO <| encodeType expected)]

private structure ActionEvidence where
  evidence : Json
  roots : Array Name := #[]
  origins : NameMap Name := {}
  forced : NameMap IR.Decl := {}
  unsupported : Array String := #[]
private def originalDecl (env : Environment) (n : Name) : IO IR.Decl := do
  let some decl := findInterpreterDecl env n
    | throw <| IO.userError "original interpreter startup raw lookup found no declaration"
  unless decl.name == n && decl.getInfo.sorryDep?.isNone do
    throw <| IO.userError "startup raw declaration identity or sorry dependency"
  checkedIO <| checkDecl decl
  return decl
private def namedEvidence (env : Environment) (target action : Name) : IO ActionEvidence := do
  let globalCI ← actualCI env target
  let actionCI ← actualCI env action
  let proof ← ioTypeProof env actionCI globalCI.type
  let globalDecl ← originalDecl env target
  let raw ← originalDecl env action
  unless getInitFnNameFor? env target == some action do
    throw <| IO.userError "actual runtime initializer does not match attribute tuple"
  let boxed := findInterpreterDeclBoxed env action
  let selected := boxed.getD raw
  checkedIO <| checkDecl selected
  unless selected.getInfo.sorryDep?.isNone do throw <| IO.userError "startup boxed declaration depends on sorry"
  let mut unsupported := #[]
  unless !globalDecl.isExtern && globalDecl.params.isEmpty &&
      (globalDecl.resultType == .object || globalDecl.resultType == .tobject) do
    unsupported := unsupported.push "named-global-not-object-or-tobject-nullary-fdecl"
  unless !raw.isExtern && raw.params.size == 1 && raw.params[0]!.ty == .void &&
      !raw.params[0]!.borrow && raw.resultType == .object do
    unsupported := unsupported.push "named-action-not-owned-void-to-object-raw-fdecl"
  unless !selected.isExtern && selected.params.size == 1 &&
      !selected.params[0]!.borrow && boxedLane selected.params[0]!.ty && selected.resultType == .object do
    unsupported := unsupported.push "original-boxed-action-ABI-outside-profile"
  let some owner := origin env action | throw <| IO.userError "initializer action has no actual module origin"
  return { evidence := Json.mkObj [
      ("kind", toJson "named-global"), ("targetCI", ← ciJson globalCI),
      ("actionCI", ← ciJson actionCI), ("ioPayloadTypeProof", proof),
      ("globalRaw", abiJson globalDecl), ("actionRaw", abiJson raw),
      ("interpreterCallable", abiJson selected),
      ("interpreterSelection", toJson (if boxed.isSome then "original-interpreter-boxed-lookup" else "original-raw-fallback")),
      ("javaTransactionRoute", Json.mkObj [("name", nameJson raw.name),
        ("world", toJson "canonical-erased-unit-zero"),
        ("relationship", toJson "original-raw-not-the-boxed-selection"),
        ("boxedBridgeStructuralValidation", toJson "required-before-Java-activation")])],
    roots := #[target, raw.name, selected.name],
    origins := ({} : NameMap Name).insert selected.name owner,
    forced := (({} : NameMap IR.Decl).insert target globalDecl).insert raw.name raw |>.insert selected.name selected,
    unsupported }
private def anonymousEvidence (env : Environment) (action : Name) : IO ActionEvidence := do
  let ci ← actualCI env action
  let proof ← ioTypeProof env ci (mkConst ``Unit)
  let raw ← originalDecl env action
  let boxed := findInterpreterDeclBoxed env action
  let selected := boxed.getD raw
  checkedIO <| checkDecl selected
  let some owner := origin env action | throw <| IO.userError "anonymous action has no actual module origin"
  return { evidence := Json.mkObj [("kind", toJson "anonymous-io-unit"),
      ("actionCI", ← ciJson ci), ("ioPayloadTypeProof", proof),
      ("actionRaw", abiJson raw), ("interpreterCallable", abiJson selected)],
    roots := #[raw.name, selected.name], origins := ({} : NameMap Name).insert selected.name owner,
    forced := (({} : NameMap IR.Decl).insert raw.name raw).insert selected.name selected,
    unsupported := #["anonymous-regular-activation-not-supported-in-v1"] }

private def userErrorEvidence (env : Environment) : IO ActionEvidence := do
  let n := ``IO.userError
  let ci ← actualCI env n
  let ((actual, expected), _, _) ← (do
    let expected := mkArrow (mkConst ``String) (mkConst ``IO.Error)
    unless ← Meta.withTransparency .default (Meta.isDefEq ci.type expected) do
      throwError "actual IO.userError type differs from String to IO.Error"
    pure (← instantiateMVars ci.type, ← instantiateMVars expected) : MetaM (Expr × Expr)).toIO
      { fileName := "<native-startup-user-error>", fileMap := default,
        maxRecDepth := 256, maxHeartbeats := 200000 } { env }
  let raw ← originalDecl env n
  unless !raw.isExtern && raw.params.size == 1 && boxedLane raw.params[0]!.ty && boxedLane raw.resultType do
    throw <| IO.userError "IO.userError codec raw ABI differs"
  return { evidence := Json.mkObj [("purpose", toJson "portable-entropy-io-error-user-error-codec"),
      ("name", nameJson n), ("CI", ← ciJson ci), ("raw", abiJson raw),
      ("typeProof", Json.mkObj [("algorithm", toJson "Lean.Meta.isDefEq"),
        ("transparency", toJson "default"), ("actualType", ← checkedIO <| encodeType actual),
        ("expectedType", ← checkedIO <| encodeType expected)]),
      ("notAnInitializerAction", toJson true),
      ("consumerRawConstructorBodyCheck", toJson "required")],
    roots := #[n], forced := ({} : NameMap IR.Decl).insert n raw }

private partial def checkModuleName : Name → Except String Unit
  | .anonymous => pure ()
  | .num .. => throw "module Name cannot have a numeric component"
  | .str parent leaf => do
    unless !leaf.isEmpty && leaf != "." && leaf != ".." &&
        !(leaf.toList.any fun c => c == '/' || c == '\\' || c.toNat == 0) do
      throw "module Name has an invalid filesystem component"
    checkModuleName parent
private def readRequest (path : String) : IO (Json × Array Import) := do
  let document ← checkedIO <| Json.parse (← readBounded path 65536)
  unless (← checkedIO <| document.getObjValAs? String "schema") == "lean-native-startup-requests/1" &&
      (← checkedIO <| document.getObjValAs? String "profile") == "legacy-private-ordinary/1" do
    throw <| IO.userError "unsupported startup request schema/profile"
  let values ← checkedIO <| (← checkedIO <| document.getObjVal? "requestedImports").getArr?
  unless 1 ≤ values.size && values.size ≤ 128 do throw <| IO.userError "requested import count bound"
  let mut imports : Array Import := #[]
  for value in values do
    let n ← checkedIO <| checkedName (← checkedIO <| value.getObjVal? "module")
    checkedIO <| checkModuleName n
    let importAll ← checkedIO <| value.getObjValAs? Bool "importAll"
    let isExported ← checkedIO <| value.getObjValAs? Bool "isExported"
    let isMeta ← checkedIO <| value.getObjValAs? Bool "isMeta"
    unless !n.isAnonymous && !importAll && isExported && !isMeta do
      throw <| IO.userError "startup v1 requires nonanonymous ordinary legacy requested imports"
    imports := imports.push { module := n, importAll, isExported, isMeta }
  return (document, imports)

unsafe def exportStartup (requestPath : String) : IO Json := do
  initSearchPath (← findSysroot)
  let (request, imports) ← readRequest requestPath
  let opts : Options := {}
  enableInitializersExecution
  -- This native import may itself execute native initializers. It establishes
  -- source metadata, not a receipt that the future Java branch ran an action.
  let env ← importModules imports opts (loadExts := true) (level := .private)
  unless !env.header.isModule && env.header.imports == imports && env.header.modules.size ≤ 4096 do
    throw <| IO.userError "actual imported environment differs from requested legacy profile"
  let mut moduleEvidence := #[]
  let mut selectedActions := #[]
  let mut unsupported := #[]
  let mut roots := #[]
  let mut origins : NameMap Name := {}
  let mut forced : NameMap IR.Decl := {}
  let mut occurrences := 0
  let mut actionCount := 0
  let mut namedTargets : NameSet := {}
  for module in env.header.modules, index in [:env.header.modules.size] do
    let regular := regularInitAttr.ext.getModuleEntries env index
    let regularIR := regularInitAttr.ext.getModuleIREntries env index
    let builtin := builtinInitAttr.ext.getModuleEntries env index
    let builtinIR := builtinInitAttr.ext.getModuleIREntries env index
    occurrences := occurrences + regular.size + regularIR.size + builtin.size + builtinIR.size
    unless occurrences ≤ 16384 do throw <| IO.userError "startup attribute occurrence bound"
    let (_, _) ← checkedIO <| (do
      checkName module.module
      for (decl, init) in regular ++ regularIR ++ builtin ++ builtinIR do
        checkName decl
        checkName init).run {}
    -- Preserve the first list AS IS. Only appended IR pairs are filtered against
    -- the original first list, exactly as pinned runInitAttrForMod does.
    let sequence := regularSequence regular regularIR
    let initRuntime := Elab.inServer.get opts || module.irPhases != .runtime
    let mut decisions := #[]
    if !builtin.isEmpty || !builtinIR.isEmpty then
      unsupported := unsupported.push <| Json.mkObj [("moduleIndex", toJson index),
        ("module", nameJson module.module), ("reason", toJson "builtin-initialization-obligations-not-supported-in-v1")]
    for pair in sequence, ordinal in [:sequence.size] do
      let (target, init) := pair
      let declarationPhase := getIRPhases env target
      let selected := phaseSelected (Elab.inServer.get opts) module.irPhases declarationPhase
      decisions := decisions.push <| Json.mkObj [("ordinal", toJson ordinal),
        ("pair", toJson pair), ("declarationIRPhases", phaseJson declarationPhase),
        ("selected", toJson selected)]
      if !selected then continue
      actionCount := actionCount + 1
      unless actionCount ≤ 2048 do throw <| IO.userError "selected startup action bound"
      if !init.isAnonymous then
        if namedTargets.contains target then
          unsupported := unsupported.push <| Json.mkObj [("moduleIndex", toJson index),
            ("module", nameJson module.module), ("sequenceOrdinal", toJson ordinal),
            ("pair", toJson pair), ("reason", toJson "repeated-named-target-not-supported-by-v1-transaction")]
        namedTargets := namedTargets.insert target
      let action ← if init.isAnonymous then anonymousEvidence env target else namedEvidence env target init
      let record := Json.mkObj [("moduleIndex", toJson index), ("module", nameJson module.module),
        ("sequenceOrdinal", toJson ordinal), ("pair", toJson pair), ("evidence", action.evidence)]
      selectedActions := selectedActions.push record
      for reason in action.unsupported do
        unsupported := unsupported.push <| Json.mkObj [("moduleIndex", toJson index),
          ("module", nameJson module.module), ("sequenceOrdinal", toJson ordinal),
          ("pair", toJson pair), ("reason", toJson reason)]
      roots := roots ++ action.roots
      for (name, owner) in action.origins do
        if let some previous := origins.find? name then
          unless previous == owner do throw <| IO.userError "conflicting startup declaration origin"
        origins := origins.insert name owner
      for (name, decl) in action.forced do
        if let some previous := forced.find? name then
          unless toJson previous == toJson decl do throw <| IO.userError "conflicting startup canonical declaration"
        forced := forced.insert name decl
    moduleEvidence := moduleEvidence.push <| Json.mkObj [("index", toJson index),
      ("effectiveImport", effectiveJson module), ("initRuntime", toJson initRuntime),
      ("regularModuleEntries", toJson regular), ("regularIREntries", toJson regularIR),
      ("builtinModuleEntries", toJson builtin), ("builtinIREntries", toJson builtinIR),
      ("regularSequence", toJson sequence), ("phaseDecisions", Json.arr decisions)]
  let auxiliary ← userErrorEvidence env
  roots := roots ++ auxiliary.roots
  for (name, decl) in auxiliary.forced do
    if let some previous := forced.find? name then
      unless toJson previous == toJson decl do throw <| IO.userError "conflicting auxiliary canonical declaration"
    forced := forced.insert name decl
  let (declarations, dynamic) ← rows env roots origins forced
  return Json.mkObj [("schema", toJson "lean-native-startup-evidence/1"),
    ("leanCommit", toJson Lean.githash), ("leanVersion", toJson Lean.versionString),
    ("producer", toJson "NativeStartupEvidence.exportStartup"), ("request", request),
    ("profile", toJson "legacy-private-ordinary/1"),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits), ("target", toJson System.Platform.target)]),
    ("requestedImports", Json.arr (imports.map importJson)),
    ("actualHeader", Json.mkObj [("isModule", toJson env.header.isModule),
      ("imports", Json.arr (env.header.imports.map importJson)), ("globalLevel", toJson "private"),
      ("inServer", toJson (Elab.inServer.get opts))]),
    ("moduleOrder", toJson env.header.moduleNames), ("modules", Json.arr moduleEvidence),
    ("selectedActions", Json.arr selectedActions), ("unsupportedActivationReasons", Json.arr unsupported),
    ("auxiliaryRoots", Json.arr #[auxiliary.evidence]), ("closureRoots", toJson roots),
    ("declarations", Json.arr declarations), ("dynamicAPSites", toJson dynamic),
    ("dynamicClosureProven", toJson false), ("nativeImportMayExecuteInitializers", toJson true),
    ("additionalNativeAvailabilityProbePerformed", toJson false),
    ("nativeImportInitializationStatusReceipt", Json.null),
    ("selectionScope", toJson "regular-interpreted-fallback-if-native-module-init-unavailable"),
    ("javaInitializationExecuted", toJson false), ("guestKernelAdmission", toJson false)]

def exportHeader (path : String) : IO Json := do
  let contents ← readBounded path 1048576
  let input := Parser.mkInputContext contents path (normalizeLineEndings := false)
  let (header, state, messages) ← Parser.parseHeader input
  unless state.pos.byteIdx ≤ contents.utf8ByteSize do throw <| IO.userError "header parser position outside source"
  unless messages.reported.size + messages.unreported.size ≤ 64 do
    throw <| IO.userError "header diagnostic count exceeds bound"
  let mut diagnostics := #[]
  let mut diagnosticBytes := 0
  for message in messages.toList do
    let diagnostic ← Message.toJson message
    diagnosticBytes := diagnosticBytes + diagnostic.compress.utf8ByteSize
    unless diagnosticBytes ≤ 262144 do throw <| IO.userError "header diagnostics exceed byte bound"
    diagnostics := diagnostics.push diagnostic
  let common := [("schema", toJson "lean-project-header/2"),
    ("producer", toJson "NativeStartupEvidence.exportHeader"),
    ("leanCommit", toJson Lean.githash), ("leanVersion", toJson Lean.versionString),
    ("fileName", toJson path), ("sourceUTF8Bytes", toJson contents.utf8ByteSize),
    ("lineEndingNormalization", toJson "disabled"), ("parserEndByte", toJson state.pos.byteIdx),
    ("parserHasErrors", toJson messages.hasErrors), ("diagnostics", Json.arr diagnostics)]
  if messages.hasErrors then return Json.mkObj <| common ++ [("header", Json.null)]
  let `(Parser.Module.header| $[module%$moduleTk]? $[prelude%$preludeTk]? $importsStx*) := header
    | throw <| IO.userError "original successful header syntax has unexpected shape"
  let explicit := Elab.HeaderSyntax.imports header (includeInit := false)
  let requested := Elab.HeaderSyntax.imports header
  unless explicit.size == importsStx.size && explicit.size ≤ requested.size && requested.size ≤ 4096 do
    throw <| IO.userError "header import provenance count mismatch/bound"
  let mut positions := #[]
  for stx in importsStx do
    positions := positions.push <| Json.mkObj [("startByte", toJson (stx.raw.getPos?.map (·.byteIdx))),
      ("endByte", toJson (stx.raw.getTailPos?.map (·.byteIdx)))]
  return Json.mkObj <| common ++ [("header", Json.mkObj [
    ("isModule", toJson (!moduleTk.isNone)), ("hasPrelude", toJson (!preludeTk.isNone)),
    ("explicitImports", Json.arr (explicit.map importJson)),
    ("explicitImportSpans", Json.arr positions),
    ("requestedImports", Json.arr (requested.map importJson)),
    ("insertedImportPrefix", Json.arr ((requested.extract 0 (requested.size - explicit.size)).map importJson)),
    ("interpretation", toJson "original-HeaderSyntax.imports-includeInit-false-and-true")])]

end NativeStartupEvidence

unsafe def main (args : List String) : IO Unit := do
  let result ← match args with
    | ["--header", path] => NativeStartupEvidence.exportHeader path
    | ["--startup", path] => NativeStartupEvidence.exportStartup path
    | _ => throw <| IO.userError "usage: --header SOURCE | --startup REQUEST.json"
  let output := result.compress
  unless output.utf8ByteSize ≤ 16777216 do throw <| IO.userError "startup evidence output exceeds 16MiB"
  IO.println output

