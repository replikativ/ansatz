import Lean.Meta.Check
import Lean.Meta.ExprDefEq
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.ToIRType
import Lean.Compiler.InitAttr
import Lean.Compiler.ClosedTermCache
import Lean.Compiler.ExportAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.LCNF.SimpleGroundExpr
import Lean.Compiler.LCNF.ToImpureType
import Lean.Elab.Deriving.FromToJson

/-!
New transport for the private v3 campaign. Copied from immutable v2 source
9aab83d109979676c7f4f9657366548dca774b3ffefc83806d3e76697fca6b9a;
no change to that source, its imports, bundles or admitted pairs. Exports bounded
native observations only; no public cohort or constructor authority is issued.
-/
open Lean
namespace NativeEntryTransport

def nameJson : Name → Json
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
def encodeType (e : Expr) : Except String Json := do
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
def checkedName (j : Json) : Except String Name := do
  let n ← decodeName j 0
  let (_, _) ← (checkName n).run {}
  return n

def checkedIO {α} (v : Except String α) : IO α :=
  match v with
  | .ok a => pure a
  | .error message => throw <| IO.userError message
def readBounded (path : String) (limit : Nat) : IO String :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    repeat
      let chunk ← handle.read 4096
      if chunk.isEmpty then break
      unless bytes.size + chunk.size ≤ limit do throw <| IO.userError "input byte bound exceeded"
      bytes := bytes ++ chunk
    let some text := String.fromUTF8? bytes | throw <| IO.userError "input is not exact UTF-8"
    return text

-- Actual pinned original interpreter lookup, including base-module-index boxed
-- lookup. Do not replace this with mkBoxedName or a display/suffix heuristic.
@[extern "lean_ir_find_env_decl"]
opaque findInterpreterDecl (env : Environment) (name : Name) : Option IR.Decl
@[extern "lean_ir_find_env_decl_boxed"]
opaque findInterpreterDeclBoxed (env : Environment) (name : Name) : Option IR.Decl

def boxedLane : IR.IRType → Bool
  | .object | .tobject | .tagged => true
  | _ => false
def origin (env : Environment) (n : Name) : Option Name :=
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

def abiJson (d : IR.Decl) : Json :=
  Json.mkObj [("name", nameJson d.name), ("xs", toJson d.params), ("type", toJson d.resultType)]


def fieldLayoutJson : Compiler.LCNF.CtorFieldInfo → Json
  | .erased => Json.mkObj [("kind", toJson "erased")]
  | .void => Json.mkObj [("kind", toJson "void")]
  | .object index type => Json.mkObj [("kind", toJson "object"), ("index", toJson index),
      ("irType", toJson (IR.toIRType type))]
  | .usize index => Json.mkObj [("kind", toJson "usize"), ("index", toJson index)]
  | .scalar bytes offset type => Json.mkObj [("kind", toJson "scalar"),
      ("bytes", toJson bytes), ("offset", toJson offset), ("irType", toJson (IR.toIRType type))]


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
def checkDecl (d : IR.Decl) : Except String Unit := do
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


def rows (env : Environment) (roots : Array Name) (origins : NameMap Name)
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

def initializerInventory (env : Environment) : IO (Array Json) := do
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


end NativeEntryTransport
