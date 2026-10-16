import Lean

open Lean

-- A pinned, structural schema: Name has a stock string-based JSON encoder, so
-- override it locally to preserve numeric components and avoid ambiguous names.
private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", encodeName p, toJson s]
  | .num p n => Json.arr #[toJson "num", encodeName p, toJson (toString n)]

local instance : ToJson Name := ⟨encodeName⟩
deriving instance ToJson for IR.VarId, IR.JoinPointId, IR.IRType, IR.Arg, IR.LitVal,
  IR.CtorInfo, IR.Expr, IR.Param, IR.DeclInfo, ExternEntry, ExternAttrData

private def node (op : String) (args : Array Json) : Json :=
  Json.arr (#[toJson op] ++ args)

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
  | .case t x ty cs => node "case" #[encodeName t, toJson x, toJson ty, Json.arr (cs.map altJson)]
  | .ret x => node "ret" #[toJson x]
  | .jmp j ys => node "jmp" #[toJson j, toJson ys]
  | .unreachable => node "unreachable" #[]
private partial def altJson : IR.Alt → Json
  | .ctor i b => node "ctor" #[toJson i, bodyJson b]
  | .default b => node "default" #[bodyJson b]
end

local instance : ToJson IR.FnBody := ⟨bodyJson⟩
deriving instance ToJson for IR.Decl

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

private def emit (env : Environment) (n : Name) : IO (Array Name) := do
  match IR.findEnvDecl env n with
  | none =>
    IO.println <| (Json.mkObj [("kind", toJson "missing"), ("name", encodeName n)]).compress
    return #[]
  | some d =>
    let deps := match d with
      | .fdecl (body := b) .. => bodyDeps b
      | _ => #[]
    IO.println <| (Json.mkObj [("kind", toJson "decl"), ("name", encodeName n), ("ir", toJson d),
      ("dependencies", toJson deps), ("pretty", toJson (IR.formatDecl d).pretty)]).compress
    return deps

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let closure := args.head? == some "--closure"
  let args := if closure then args.drop 1 else args
  let mod := (args.headD "Init.Prelude").toName
  let env ← importModules #[{ module := mod, importAll := true, isMeta := true }] {}
    (loadExts := true) (level := .private)
  let names := if args.length > 1 then args.drop 1 else ["Nat.add", "List.map"]
  let mut modules := #[]
  for m in env.header.modules, i in [:env.header.modules.size] do
    let entries := IR.declMapExt.getModuleIREntries env i
    let inits := regularInitAttr.ext.getModuleEntries env i
    let inits := inits ++ (regularInitAttr.ext.getModuleIREntries env i).filter (!inits.contains ·)
    let builtinInits := builtinInitAttr.ext.getModuleEntries env i
    modules := modules.push <| Json.mkObj [("module", encodeName m.module),
      ("irDeclarations", toJson entries.size), ("initializers", toJson inits),
      ("builtinInitializers", toJson builtinInits)]
  IO.println <| (Json.mkObj [("kind", toJson "manifest"), ("schema", toJson "lean-ir-probe/1"),
    ("leanVersion", toJson Lean.versionString), ("modules", Json.arr modules)]).compress
  let mut pending := names.toArray.map String.toName
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let deps ← emit env n
    if closure then pending := pending ++ deps
