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

private def exportTargets (env : Environment) : Std.HashMap String Name := Id.run do
  let mut targets := {}
  for (n, _) in env.constants.toList do
    if let some exportName := getExportNameFor? env n then
      let symbol := exportName.toString
      if symbol == "lean_eval_check_meta" || symbol == "lean_is_reserved_name" then
        targets := targets.insert symbol n
  return targets

private def emit (sourceEnv : Environment) (importedEnv? : Option Environment) (exports : Std.HashMap String Name) (n : Name) : IO (Array Name) := do
  -- Source compilation does not load every private imported initializer body.
  -- Keep local declarations in their original environment; use a full-visibility
  -- import environment only for imported declarations, never replace local IR.
  let local? := (IR.declMapExt.getState sourceEnv).find? n
  let imported? := importedEnv?.bind fun fallback => IR.findEnvDecl fallback n
  let env := if local?.isSome || imported?.isNone then sourceEnv else importedEnv?.getD sourceEnv
  let decl? := local? <|> imported? <|> IR.findEnvDecl sourceEnv n
  match decl? with
  | none =>
    IO.println <| (Json.mkObj [("kind", toJson "missing"), ("name", encodeName n)]).compress
    return #[]
  | some d =>
    let redirect? := match d with
      | .extern _ _ _ ext => do
        let .standard _ symbol ← getExternEntryFor ext `c | none
        let target ← exports[symbol]?
        guard (target != n)
        let targetDecl ← IR.findEnvDecl env target <|> (importedEnv?.bind fun fallback => IR.findEnvDecl fallback target)
        let .fdecl .. := targetDecl | none
        some (target, Json.mkObj [("name", encodeName target),
          ("params", toJson targetDecl.params), ("type", toJson targetDecl.resultType)])
      | _ => none
    let initFn := getInitFnNameFor? env n
    let role := if initFn.isSome then "initialized"
      else if isClosedTermName env n then "closed"
      else if Compiler.LCNF.isSimpleGroundDecl env n then "ground"
      else if d.params.isEmpty then "value"
      else "ordinary"
    let deps := (match d with
      | .fdecl (body := b) .. => bodyDeps b
      | _ => #[]) ++ initFn.toArray ++ (redirect?.map (·.1)).toArray
    IO.println <| (Json.mkObj [("kind", toJson "decl"), ("name", encodeName n), ("ir", toJson d),
      ("dependencies", toJson deps),
      ("sourceLocal", toJson local?.isSome), ("sourceModule", toJson (if local?.isSome then some sourceEnv.mainModule else none)),
      ("redirect", toJson (redirect?.map (·.2))),
      ("runtime", Json.mkObj [("role", toJson role), ("initializer", toJson initFn)]), ("pretty", toJson (IR.formatDecl d).pretty)]).compress
    return deps

-- Record initialization while the compiler's nonserialized declaration order
-- and closed/ground classifications still exist. Match LCNF.EmitC, not name sort.
private def sourceInitPlan : CoreM (Json × Array Name) := do
  let env ← getEnv
  let names ← Compiler.LCNF.getLocalImpureDecls
  let indices := Compiler.LCNF.getImpureDeclIndices env names
  let names := names.qsort fun l r => indices[l]! < indices[r]!
  let mut actions := #[]
  let mut roots := #[]
  for n in names do
    let some d ← Compiler.LCNF.getLocalImpureDecl? n | continue
    let action? :=
      if isIOUnitInitFn env n then
        some <| Json.mkObj [("kind", toJson "io"), ("name", encodeName n), ("target", encodeName n)]
      else if d.params.isEmpty then
        if let some initFn := getInitFnNameFor? env n then
          some <| Json.mkObj [("kind", toJson "initialize"), ("name", encodeName n), ("target", encodeName initFn)]
        else if !(isClosedTermName env n || Compiler.LCNF.isSimpleGroundDecl env n) then
          some <| Json.mkObj [("kind", toJson "value"), ("name", encodeName n), ("target", encodeName n)]
        else none
      else none
    if let some action := action? then
      roots := roots.push n
      actions := actions.push <| Json.mkObj [("action", action), ("meta", toJson (isMarkedMeta env n))]
  return (Json.mkObj [("kind", toJson "initialization-plan"), ("schema", toJson "lean-init-plan/1"),
    ("moduleSystem", toJson env.header.isModule), ("module", encodeName env.mainModule),
    ("imports", toJson (env.imports.map fun imp => Json.mkObj [("module", encodeName imp.module), ("meta", toJson imp.isMeta)])), ("actions", Json.arr actions)], roots)

-- Opt-in structural module transport. Everything below except module argument
-- decoding is retained from the accepted Export.lean source.
private partial def decodeModule (j : Json) (depth : Nat := 0) : Except String Name := do
  unless depth < 65 do throw "module Name depth bound"
  let a ← j.getArr?
  if a == #[toJson "anonymous"] then return .anonymous
  unless a.size == 3 && a[0]! == toJson "str" do throw "module requires string Name components"
  let parentName ← decodeModule a[1]! (depth + 1)
  let leaf ← a[2]!.getStr?
  unless !leaf.isEmpty && leaf.utf8ByteSize ≤ 255 && leaf != "." && leaf != ".." &&
      !leaf.contains '/' && !leaf.contains '\\' && !leaf.contains (Char.ofNat 0) do
    throw "invalid module path component"
  return .str parentName leaf

private def moduleArgument (text : String) : IO Name := do
  unless text.utf8ByteSize ≤ 16384 do throw <| IO.userError "typed module argument byte bound"
  let parsed := do
    let json ← Json.parse text
    let name ← decodeModule json
    if name.isAnonymous then throw "anonymous module is not supported"
    pure name
  match parsed with
  | .ok name => pure name
  | .error error => throw <| IO.userError error

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let sourceMode := args.head? == some "--source"
  let args := if sourceMode then args.drop 1 else args
  let sourcePath := args.headD ""
  let args := if sourceMode then args.drop 1 else args
  let outputOlean := args.head? == some "--olean"
  let oleanPath? := if outputOlean then args[1]? else none
  let args := if outputOlean then args.drop 2 else args
  let closure := args.head? == some "--closure"
  let args := if closure then args.drop 1 else args
  let localOnly := args.head? == some "--local"
  let args := if localOnly then args.drop 1 else args
  if localOnly && !sourceMode then throw <| IO.userError "--local requires --source"
  unless sourceMode && outputOlean && localOnly && args.length == 2 && args.head? == some "--typed-module" do
    throw <| IO.userError "usage: --source SOURCE --olean OUTPUT --local --typed-module STRUCTURAL_NAME_JSON"
  let mod ← moduleArgument (args[1]!)
  let env ← if sourceMode then do
      let input ← IO.FS.readFile sourcePath
      -- The original frontend reports warnings, info and errors on current stdout.
      -- Keep them visible on stderr; withStdout restores the structural output
      -- stream in finally, including when the frontend throws or returns none.
      let frontend? ← IO.withStdout (← IO.getStderr) <|
        Elab.runFrontend input {} sourcePath mod (oleanFileName? := oleanPath?.map System.FilePath.mk)
      let some env := frontend?
        | throw <| IO.userError "Source frontend failed; no initialization plan exported"
      pure env
    else
      importModules #[{ module := mod, importAll := true, isMeta := true }] {}
        (loadExts := true) (level := .private)
  let names := if args.length > 1 then args.drop 1 else ["Nat.add", "List.map"]
  let mut modules := #[]
  for m in (if localOnly then #[] else env.header.modules), i in [:env.header.modules.size] do
    let entries := IR.declMapExt.getModuleIREntries env i
    let inits := regularInitAttr.ext.getModuleEntries env i
    let inits := inits ++ (regularInitAttr.ext.getModuleIREntries env i).filter (!inits.contains ·)
    let builtinInits := builtinInitAttr.ext.getModuleEntries env i
    modules := modules.push <| Json.mkObj [("module", encodeName m.module),
      ("irDeclarations", toJson entries.size), ("initializers", toJson inits),
      ("builtinInitializers", toJson builtinInits)]
  let (plan?, initRoots) ← if sourceMode then do
      let (plan, roots) ← sourceInitPlan.toIO' { fileName := sourcePath, fileMap := default } { env }
      pure (some plan, roots)
    else pure (none, #[])
  -- The plan is in the manifest so existing declaration-stream readers keep
  -- treating every subsequent row as a declaration.
  let exports := exportTargets env
  IO.println <| (Json.mkObj [("kind", toJson "manifest"), ("schema", toJson "lean-ir-probe/1"),
    ("leanVersion", toJson Lean.versionString),
    ("initializationPlan", toJson plan?),
    ("exports", toJson (exports.toArray.map fun (symbol, name) => Json.mkObj [("symbol", toJson symbol), ("name", encodeName name)])),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits),
      ("target", toJson System.Platform.target)]), ("modules", Json.arr modules)]).compress
  let importedEnv? ← if sourceMode && !localOnly then do
      enableInitializersExecution
      let imports := env.imports.map fun imp => { module := imp.module, importAll := true, isMeta := true : Import }
      let imported ← importModules imports {} (loadExts := true) (level := .private)
      pure (some imported)
    else pure none
  let exports := if let some imported := importedEnv? then (exportTargets imported).fold (fun m k v => m.insert k v) exports else exports
  let requested := if localOnly then (IR.declMapExt.getState env).toArray.map (·.1) else names.toArray.map String.toName
  let mut pending := requested ++ initRoots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let deps ← emit env importedEnv? exports n
    if closure then pending := pending ++ deps
