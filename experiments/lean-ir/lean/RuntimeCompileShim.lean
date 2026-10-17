import Lean.Elab.Frontend
import Lean.Compiler.IR.Format
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.SimpleGroundExpr
import Lean.Compiler.ClosedTermCache

open Lean

namespace RuntimeCompileShim

-- Structural runtime handoff, using the same pinned schema as Export.lean.
-- This code runs against the supplied guest environment; it imports no files,
-- spawns no native compiler, and does not evaluate generated declarations.
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


private def exportTargets (env : Environment) : Std.HashMap String Name := Id.run do
  let mut targets := {}
  for (name, _) in env.constants.toList do
    if let some symbol := getExportNameFor? env name then
      targets := targets.insert symbol.toString name
  return targets

private def declarationRow (env : Environment) (exports : Std.HashMap String Name)
    (name : Name) (decl : IR.Decl) : Json × Array Name := Id.run do
  let local? := (IR.declMapExt.getState env).contains name
  let redirect? := match decl with
    | .extern _ _ _ ext => do
      let .standard _ symbol ← getExternEntryFor ext `c | none
      let target ← exports[symbol]?
      guard (target != name)
      let targetDecl ← IR.findEnvDecl env target
      let .fdecl .. := targetDecl | none
      some (target, Json.mkObj [("name", encodeName target),
        ("params", toJson targetDecl.params), ("type", toJson targetDecl.resultType)])
    | _ => none
  let initializer := getInitFnNameFor? env name
  let role := if initializer.isSome then "initialized"
    else if isClosedTermName env name then "closed"
    else if Compiler.LCNF.isSimpleGroundDecl env name then "ground"
    else if decl.params.isEmpty then "value" else "ordinary"
  let dependencies := (match decl with
    | .fdecl (body := body) .. => bodyDeps body
    | _ => #[]) ++ initializer.toArray ++ (redirect?.map (·.1)).toArray
  let row := Json.mkObj [
    ("kind", toJson "decl"), ("name", encodeName name), ("ir", toJson decl),
    ("dependencies", toJson dependencies), ("sourceLocal", toJson local?),
    ("sourceModule", toJson (if local? then some env.mainModule else none)),
    ("redirect", toJson (redirect?.map (·.2))),
    ("runtime", Json.mkObj [("role", toJson role), ("initializer", toJson initializer)]),
    ("pretty", toJson (IR.formatDecl decl).pretty)]
  return (row, dependencies)

/-- Export a dependency-closed structural IR bundle from an already elaborated
runtime environment. Roots also include their actual boxed wrappers when present.
Missing bodies are explicit rows, never fabricated extern declarations. The
caller must reconcile those names with its existing linked/import catalogue.
The initialization plan describes local source actions; it is not permission to
repeat initialization effects that the running frontend already performed. -/
@[noinline] def exportCompiled (env : Environment) (roots : Array Name) : IO String := do
  let (plan, initRoots) ← sourceInitPlan.toIO'
    { fileName := "RuntimeCompileShim", fileMap := default } { env }
  let exports := exportTargets env
  let mut pending := roots ++ initRoots
  let mut entries := #[]
  for root in roots do
    let boxed := Compiler.LCNF.mkBoxedName root
    let boxed? := (IR.findEnvDecl env boxed).map (fun _ => boxed)
    if let some boxed := boxed? then pending := pending.push boxed
    entries := entries.push <| Json.mkObj [
      ("name", encodeName root), ("boxedTarget", encodeName (boxed?.getD root))]
  let mut rows := #[]
  let mut seen : NameSet := {}
  let mut missing := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    match IR.findEnvDecl env name with
    | none =>
      missing := missing.push name
      rows := rows.push <| Json.mkObj [("kind", toJson "missing"), ("name", encodeName name)]
    | some decl =>
      let (row, dependencies) := declarationRow env exports name decl
      rows := rows.push row
      pending := pending ++ dependencies
  let manifest := Json.mkObj [
    ("kind", toJson "manifest"), ("schema", toJson "lean-ir-probe/1"),
    ("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
    ("producer", toJson "RuntimeCompileShim.exportCompiled"),
    ("initializationPlan", plan), ("initializationPlanScope", toJson "all-local-declarations"),
    ("requestedRoots", toJson roots),
    ("entryPoints", Json.arr entries), ("missingDependencies", toJson missing),
    ("exports", toJson (exports.toArray.map fun (symbol, name) =>
      Json.mkObj [("symbol", toJson symbol), ("name", encodeName name)])),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits),
      ("target", toJson System.Platform.target)]),
    ("modules", Json.arr #[])]
  return String.intercalate "\n" ((#[manifest] ++ rows).toList.map Json.compress) ++ "\n"

/-- These redirect to the actual pinned Lean interpreter lookup bodies in the
hosted runtime. Unlike `IR.findEnvDecl`, they consult module IR entries before
ordinary imported entries and resolve boxed names using the base module index. -/
@[extern "lean_ir_find_env_decl"]
private opaque findInterpreterDecl (env : Environment) (name : Name) : Option IR.Decl
@[extern "lean_ir_find_env_decl_boxed"]
private opaque findInterpreterDeclBoxed (env : Environment) (name : Name) : Option IR.Decl

/-- Witness selected from the caller's actual guest IR environment. A host may
reuse protected code only after comparing these complete declarations with its
pinned catalogue, never merely because a name or kernel root matches. -/
@[noinline] def exportEvalConstWitness (env : Environment) (name : Name) : IO String := do
  let selected := findInterpreterDecl env name
  let boxed := match selected with
    | some decl => if decl.params.isEmpty then none else findInterpreterDeclBoxed env name
    | none => none
  let mut forced : NameMap IR.Decl := {}
  if let some decl := selected then forced := forced.insert name decl
  if let some decl := boxed then forced := forced.insert decl.name decl
  let mut pending := #[name] ++ (boxed.map (·.name)).toArray
  let mut seen : NameSet := {}
  let mut rows := #[]
  let mut missing := #[]
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    if seen.contains current then continue
    seen := seen.insert current
    match forced.find? current <|> findInterpreterDecl env current with
    | none => missing := missing.push current
    | some decl =>
      let moduleIdx? := env.getModuleIdxFor? (if boxed.any (·.name == current) then name else current)
      let local? := moduleIdx?.isNone
      let sourceModule := moduleIdx?.map fun idx => env.header.moduleNames[idx.toNat]!
      rows := rows.push <| Json.mkObj [("name", encodeName current),
        ("ir", toJson decl), ("sourceLocal", toJson local?),
        ("sourceModule", toJson sourceModule)]
      match decl with
      | .fdecl (body := body) .. => pending := pending ++ bodyDeps body
      | _ => pure ()
  return (Json.mkObj [
    ("schema", toJson "lean-eval-const-witness/1"),
    ("producer", toJson "RuntimeCompileShim.exportEvalConstWitness"),
    ("leanCommit", toJson Lean.githash),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits),
      ("target", toJson System.Platform.target)]),
    ("name", encodeName name), ("boxedTarget", encodeName ((boxed.map (·.name)).getD name)),
    ("declarations", Json.arr rows), ("missingDependencies", toJson missing),
    ("sorryDep", toJson (IR.getSorryDep env name))]).compress

/-- Native/guest target: the fresh Lean compiler's output is transferred without
executing evalConst or depending on a native implementation of the new function. -/
@[noinline] def seededIdentityBundle : IO String := do
  let mut env ← mkEmptyEnvironment
  for name in [`lcAny, `lcErased, `lcVoid] do
    env ← IO.ofExcept <| env.addDeclCore 1000000 1000
      (.axiomDecl {name, levelParams := [], type := mkSort (.succ .zero), isUnsafe := true}) none
      |>.mapError (fun _ => "compiler marker admission failed")
  let (compiledEnv, messages) ← Elab.process
    "def answer.{u} (α : Sort u) (x : α) : α := x\n" env {}
  if messages.hasErrors then
    throw <| IO.userError "seeded identity compilation reported errors"
  exportCompiled compiledEnv #[`answer]

/-- Compile file contents using the real header parser and incremental command
frontend. The caller supplies an environment with its imports already installed;
this first gate deliberately accepts only classic `prelude` files without
imports. It never drops an implicit Init import or treats imports as comments.
The three compiler markers remain an explicit bootstrap policy of the caller. -/
@[noinline] def compilePreludeFileBundle (env : Environment) (text fileName : String)
    (moduleName : Name) (roots : Array Name) : IO String := do
  let inputCtx := Parser.mkInputContext text fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then
    throw <| IO.userError "file header reported errors"
  if Elab.HeaderSyntax.isModule header then
    throw <| IO.userError "module-system file requires module initialization planning"
  if !(Elab.HeaderSyntax.imports header).isEmpty then
    throw <| IO.userError "file imports require an imported environment"
  let env := env.setMainModule moduleName
  let state ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env messages {})
  if state.commandState.messages.hasErrors then
    throw <| IO.userError "file elaboration reported errors"
  exportCompiled state.commandState.env roots

private def fileImportJson (i : Import) : Json := Json.mkObj [
  ("module", encodeName i.module), ("importAll", toJson i.importAll),
  ("isExported", toJson i.isExported), ("isMeta", toJson i.isMeta)]

private def fileDiagnostics (messages : MessageLog) : BaseIO (Array Json) :=
  messages.reportedPlusUnreported.toArray.mapM Message.toJson

/-- Inspect the actual pinned header parser result, including both implicit Init
imports for classic files. An erroneous header must never authorize imports. -/
@[noinline] def inspectFileHeader (text fileName : String) : IO String := do
  let inputCtx := Parser.mkInputContext text fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let imports := if messages.hasErrors then #[] else Elab.HeaderSyntax.imports header
  return (Json.mkObj [
    ("schema", toJson "lean-file-header/1"), ("producer", toJson "RuntimeCompileShim.inspectFileHeader"),
    ("leanCommit", toJson Lean.githash),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits), ("target", toJson System.Platform.target)]),
    ("fileName", toJson fileName),
    ("hasErrors", toJson messages.hasErrors), ("moduleSystem", toJson (Elab.HeaderSyntax.isModule header)),
    ("requestedImports", toJson (imports.map fileImportJson)),
    ("headerEndByte", toJson parserState.pos.byteIdx),
    ("diagnostics", Json.arr (← fileDiagnostics messages))]).compress

private def fileEnvelope (fileName : String) (moduleName : Name) (isModule : Bool)
    (imports : Array Import) (messages : MessageLog) (success : Bool)
    (stage environmentState : String) (bundle : Option String := none) : BaseIO String := do
  return (Json.mkObj [
    ("schema", toJson "lean-file-compilation/1"),
    ("producer", toJson "RuntimeCompileShim.compileImportedFileState"),
    ("leanCommit", toJson Lean.githash),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits), ("target", toJson System.Platform.target)]),
    ("fileName", toJson fileName),
    ("mainModule", encodeName moduleName), ("moduleSystem", toJson isModule),
    ("requestedImports", toJson (imports.map fileImportJson)),
    ("success", toJson success), ("stage", toJson stage),
    ("environmentState", toJson environmentState),
    ("diagnostics", Json.arr (← fileDiagnostics messages)), ("bundle", toJson bundle)]).compress

private def fileError (inputCtx : Parser.InputContext) (pos : String.Pos.Raw)
    (messages : MessageLog) (message : String) : MessageLog :=
  messages.add {fileName := inputCtx.fileName, pos := inputCtx.fileMap.toPosition pos,
                severity := .error, data := message}

/-- Compile commands against exactly the supplied imported environment. Header
inspection/import transport happens separately: this helper never loads files or
replaces the caller's imports. It runs the genuine incremental command frontend.

Header/import failures return the original owned Environment. Command errors
return the actual post-command Environment (which may contain earlier successful
commands), diagnostics, and no publishable bundle. Guest IO/code side effects are
not rolled back. Success returns the final owned Environment and a structural IR
bundle. The host must check `success` before publishing a loaded-file handle. -/
@[noinline] def compileImportedFileState (env : Environment) (text fileName : String)
    (moduleName : Name) (roots : Array Name) (opts : Options) : IO (Environment × String) := do
  let inputCtx := Parser.mkInputContext text fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let isModule := Elab.HeaderSyntax.isModule header
  if messages.hasErrors then
    return (env, ← fileEnvelope fileName moduleName isModule #[] messages false "header" "input")
  let imports := Elab.HeaderSyntax.imports header
  unless imports == env.header.imports && isModule == env.header.isModule do
    let messages := fileError inputCtx (Elab.HeaderSyntax.startPos header) messages
      "file header imports/module mode differ from the supplied imported environment"
    return (env, ← fileEnvelope fileName moduleName isModule imports messages false "imports" "input")
  let env := env.setMainModule moduleName
  let messages := Elab.checkDeprecatedImports env imports opts inputCtx
    (Elab.HeaderSyntax.startPos header) messages (headerStx? := some header)
  let messages := Elab.checkModuleNamePortability moduleName inputCtx
    (Elab.HeaderSyntax.startPos header) messages
  if messages.hasErrors then
    return (env, ← fileEnvelope fileName moduleName isModule imports messages false "module-name" "prepared")
  let state ← Elab.IO.processCommands inputCtx parserState (Elab.Command.mkState env messages opts)
  let env := state.commandState.env
  let messages := state.commandState.messages
  if messages.hasErrors then
    return (env, ← fileEnvelope fileName moduleName isModule imports messages false "commands" "after-commands")
  for root in roots do
    if (IR.findEnvDecl env root).isNone then
      let messages := fileError inputCtx (Elab.HeaderSyntax.startPos header) messages
        s!"requested executable root '{root}' has no compiled IR in this file environment"
      return (env, ← fileEnvelope fileName moduleName isModule imports messages false "exports" "after-commands")
  let bundle ← exportCompiled env roots
  return (env, ← fileEnvelope fileName moduleName isModule imports messages true "complete" "after-commands" (some bundle))

/-- String convenience view. Call `compileImportedFileState` when retaining the
actual resulting guest Environment for a file handle or subsequent elaboration. -/
@[noinline] def compileImportedFileBundle (env : Environment) (text fileName : String)
    (moduleName : Name) (roots : Array Name) (opts : Options) : IO String := do
  return (← compileImportedFileState env text fileName moduleName roots opts).2

end RuntimeCompileShim

unsafe def main : IO Unit := do
  IO.print (← RuntimeCompileShim.seededIdentityBundle)


namespace RuntimeCompileShim

-- Reopen the same exact structured Name JSON instance for this appended helper.
local instance : ToJson Name := ⟨encodeName⟩

/-- Same caller-selected witness as exportEvalConstWitness, transferred as an
owned Json value. Printing is deliberately left to the receiving host; schema,
producer, closure selection, ownership and provenance checks are unchanged. -/
@[noinline] def exportEvalConstWitnessValue (env : Environment) (name : Name) : IO Json := do
  let selected := findInterpreterDecl env name
  let boxed := match selected with
    | some decl => if decl.params.isEmpty then none else findInterpreterDeclBoxed env name
    | none => none
  let mut forced : NameMap IR.Decl := {}
  if let some decl := selected then forced := forced.insert name decl
  if let some decl := boxed then forced := forced.insert decl.name decl
  let mut pending := #[name] ++ (boxed.map (·.name)).toArray
  let mut seen : NameSet := {}
  let mut rows := #[]
  let mut missing := #[]
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    if seen.contains current then continue
    seen := seen.insert current
    match forced.find? current <|> findInterpreterDecl env current with
    | none => missing := missing.push current
    | some decl =>
      let moduleIdx? := env.getModuleIdxFor? (if boxed.any (·.name == current) then name else current)
      let local? := moduleIdx?.isNone
      let sourceModule := moduleIdx?.map fun idx => env.header.moduleNames[idx.toNat]!
      rows := rows.push <| Json.mkObj [("name", encodeName current),
        ("ir", toJson decl), ("sourceLocal", toJson local?),
        ("sourceModule", toJson sourceModule)]
      match decl with
      | .fdecl (body := body) .. => pending := pending ++ bodyDeps body
      | _ => pure ()
  return Json.mkObj [
    ("schema", toJson "lean-eval-const-witness/1"),
    ("producer", toJson "RuntimeCompileShim.exportEvalConstWitness"),
    ("leanCommit", toJson Lean.githash),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson System.Platform.numBits),
      ("target", toJson System.Platform.target)]),
    ("name", encodeName name), ("boxedTarget", encodeName ((boxed.map (·.name)).getD name)),
    ("declarations", Json.arr rows), ("missingDependencies", toJson missing),
    ("sorryDep", toJson (IR.getSorryDep env name))]

end RuntimeCompileShim


namespace RuntimeCompileShim

/-- Actual selected declarations, without IR-to-Json allocation. Object fields
precede the scalar Bool physically; this source order is part of the pinned
native layout oracle, not a host-side guessed layout. -/
structure EvalConstWitnessIRRow where
  name : Name
  decl : IR.Decl
  sourceLocal : Bool
  sourceModule : Option Name

/-- Ten object fields. Nat wordBits deliberately avoids an extra scalar-layout
boundary. The receiving projector reconstructs the existing witness envelope. -/
structure EvalConstWitnessIR where
  schema : String
  producer : String
  leanCommit : String
  wordBits : Nat
  target : String
  name : Name
  boxedTarget : Name
  rows : Array EvalConstWitnessIRRow
  missingDependencies : Array Name
  sorryDep : Option Name

/-- Same actual interpreter selection and complete static closure as both older
witness helpers. Returned Name/IR values remain owned by this result; no cache,
initialization, JSON rendering, or execution authority is introduced. -/
@[noinline] def exportEvalConstWitnessIR (env : Environment) (name : Name) : IO EvalConstWitnessIR := do
  let selected := findInterpreterDecl env name
  let boxed := match selected with
    | some decl => if decl.params.isEmpty then none else findInterpreterDeclBoxed env name
    | none => none
  let mut forced : NameMap IR.Decl := {}
  if let some decl := selected then forced := forced.insert name decl
  if let some decl := boxed then forced := forced.insert decl.name decl
  let mut pending := #[name] ++ (boxed.map (·.name)).toArray
  let mut seen : NameSet := {}
  let mut rows := #[]
  let mut missing := #[]
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    if seen.contains current then continue
    seen := seen.insert current
    match forced.find? current <|> findInterpreterDecl env current with
    | none => missing := missing.push current
    | some decl =>
      let moduleIdx? := env.getModuleIdxFor? (if boxed.any (·.name == current) then name else current)
      let local? := moduleIdx?.isNone
      let sourceModule := moduleIdx?.map fun idx => env.header.moduleNames[idx.toNat]!
      rows := rows.push {
        name := current
        decl := decl
        sourceLocal := local?
        sourceModule := sourceModule
      }
      match decl with
      | .fdecl (body := body) .. => pending := pending ++ bodyDeps body
      | _ => pure ()
  return {
    schema := "lean-eval-const-witness/1"
    producer := "RuntimeCompileShim.exportEvalConstWitness"
    leanCommit := Lean.githash
    wordBits := System.Platform.numBits
    target := System.Platform.target
    name := name
    boxedTarget := (boxed.map (·.name)).getD name
    rows := rows
    missingDependencies := missing
    sorryDep := IR.getSorryDep env name
  }

end RuntimeCompileShim


namespace RuntimeCompileShim

/-- Preorder dependency collection with one append-only output. Preserve every
occurrence and the original alternative order; no pointer/name deduplication.
This helper is separate so all original renderer/witness IR remains unchanged. -/
private def bodyDepsLinear (initial : IR.FnBody) : Array Name := Id.run do
  let mut work := #[initial]
  let mut result := #[]
  while !work.isEmpty do
    let current := work.back!
    work := work.pop
    match current with
    | .vdecl _ _ expr next =>
      match expr with
      | .fap name _ | .pap name _ => result := result.push name
      | _ => pure ()
      work := work.push next
    | .jdecl _ _ value next =>
      work := (work.push next).push value
    | .case _ _ _ alternatives =>
      let mut i := alternatives.size
      while i > 0 do
        i := i - 1
        let next := match alternatives[i]! with
          | .ctor _ body | .default body => body
        work := work.push next
    | .set _ _ _ next | .setTag _ _ next | .uset _ _ _ next |
      .sset _ _ _ _ _ next | .inc _ _ _ _ next | .dec _ _ _ _ next | .del _ next =>
      work := work.push next
    | .ret _ | .jmp _ _ | .unreachable => pure ()
  return result

/-- Oracle-only dependency arrays. The original collector is retained unchanged
and supplies an independent order/duplicate reference for the new collector. -/
@[noinline] def bodyDepsLinearProbe (body : IR.FnBody) : Array Name × Array Name :=
  (bodyDeps body, bodyDepsLinear body)

/-- Same typed witness and complete static closure, using linear dependency
collection. No cache, declaration filtering, IO initializer or code authority
change is introduced. The older typed helper remains available unchanged. -/
@[noinline] def exportEvalConstWitnessIRLinear (env : Environment) (name : Name) : IO EvalConstWitnessIR := do
  let selected := findInterpreterDecl env name
  let boxed := match selected with
    | some decl => if decl.params.isEmpty then none else findInterpreterDeclBoxed env name
    | none => none
  let mut forced : NameMap IR.Decl := {}
  if let some decl := selected then forced := forced.insert name decl
  if let some decl := boxed then forced := forced.insert decl.name decl
  let mut pending := #[name] ++ (boxed.map (·.name)).toArray
  let mut seen : NameSet := {}
  let mut rows := #[]
  let mut missing := #[]
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    if seen.contains current then continue
    seen := seen.insert current
    match forced.find? current <|> findInterpreterDecl env current with
    | none => missing := missing.push current
    | some decl =>
      let moduleIdx? := env.getModuleIdxFor? (if boxed.any (·.name == current) then name else current)
      let local? := moduleIdx?.isNone
      let sourceModule := moduleIdx?.map fun idx => env.header.moduleNames[idx.toNat]!
      rows := rows.push {
        name := current
        decl := decl
        sourceLocal := local?
        sourceModule := sourceModule
      }
      match decl with
      | .fdecl (body := body) .. => pending := pending ++ bodyDepsLinear body
      | _ => pure ()
  return {
    schema := "lean-eval-const-witness/1"
    producer := "RuntimeCompileShim.exportEvalConstWitness"
    leanCommit := Lean.githash
    wordBits := System.Platform.numBits
    target := System.Platform.target
    name := name
    boxedTarget := (boxed.map (·.name)).getD name
    rows := rows
    missingDependencies := missing
    sorryDep := IR.getSorryDep env name
  }

end RuntimeCompileShim


namespace RuntimeCompileShim

/-- Project the immutable environment header module names once per invocation.
The selected declarations, dependency walker, row order, source provenance and
all authority evidence are identical to the original typed witness. This local
array introduces no cross-invocation cache or independently trusted state. -/
@[noinline] def exportEvalConstWitnessIRSharedNames (env : Environment) (name : Name) : IO EvalConstWitnessIR := do
  let selected := findInterpreterDecl env name
  let boxed := match selected with
    | some decl => if decl.params.isEmpty then none else findInterpreterDeclBoxed env name
    | none => none
  let mut forced : NameMap IR.Decl := {}
  if let some decl := selected then forced := forced.insert name decl
  if let some decl := boxed then forced := forced.insert decl.name decl
  let mut pending := #[name] ++ (boxed.map (·.name)).toArray
  let mut seen : NameSet := {}
  let mut rows := #[]
  let mut missing := #[]
  let moduleNames := env.header.moduleNames
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    if seen.contains current then continue
    seen := seen.insert current
    match forced.find? current <|> findInterpreterDecl env current with
    | none => missing := missing.push current
    | some decl =>
      let moduleIdx? := env.getModuleIdxFor? (if boxed.any (·.name == current) then name else current)
      let local? := moduleIdx?.isNone
      let sourceModule := moduleIdx?.map fun idx => moduleNames[idx.toNat]!
      rows := rows.push {
        name := current
        decl := decl
        sourceLocal := local?
        sourceModule := sourceModule
      }
      match decl with
      | .fdecl (body := body) .. => pending := pending ++ bodyDeps body
      | _ => pure ()
  return {
    schema := "lean-eval-const-witness/1"
    producer := "RuntimeCompileShim.exportEvalConstWitness"
    leanCommit := Lean.githash
    wordBits := System.Platform.numBits
    target := System.Platform.target
    name := name
    boxedTarget := (boxed.map (·.name)).getD name
    rows := rows
    missingDependencies := missing
    sorryDep := IR.getSorryDep env name
  }


end RuntimeCompileShim
