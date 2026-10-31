import Lean
open Lean
namespace MatchedInitProducer

private structure ScalarState where
  seen : Std.HashSet USize := {}
  names : Array Name := #[]
  literals : Array Literal := #[]
  irLiterals : Array IR.LitVal := #[]
  lcnfLiterals : Array Compiler.LCNF.LitValue := #[]
  formats : Array Format := #[]

private unsafe def fresh (x : α) : StateM ScalarState Bool := do
  let p := ptrAddrUnsafe x
  if (← get).seen.contains p then return false
  modify fun s => {s with seen := s.seen.insert p}
  return true

private unsafe def scalarName (n : Name) : StateM ScalarState Unit := do
  if !(← fresh n) then return
  match n with
  | .anonymous => pure ()
  | .str p _ => scalarName p
  | .num p _ =>
    modify fun s => {s with names := s.names.push n}
    scalarName p

private unsafe def scalarLevel (l : Level) : StateM ScalarState Unit := do
  if !(← fresh l) then return
  match l with
  | .zero => pure ()
  | .succ l => scalarLevel l
  | .max a b | .imax a b => scalarLevel a; scalarLevel b
  | .param n => scalarName n
  | .mvar id => scalarName id.name

private unsafe def scalarExpr (e : Expr) : StateM ScalarState Unit := do
  if !(← fresh e) then return
  match e with
  | .fvar id => scalarName id.name
  | .mvar id => scalarName id.name
  | .const n us => scalarName n; us.forM scalarLevel
  | .sort l => scalarLevel l
  | .app f a => scalarExpr f; scalarExpr a
  | .lam n t b _ | .forallE n t b _ => scalarName n; scalarExpr t; scalarExpr b
  | .letE n t v b _ => scalarName n; scalarExpr t; scalarExpr v; scalarExpr b
  | .mdata m e =>
    for (k, v) in m.entries do
      scalarName k
      if let .ofName n := v then scalarName n
    scalarExpr e
  | .proj n _ e => scalarName n; scalarExpr e
  | .lit l =>
    if let .natVal _ := l then modify fun s => {s with literals := s.literals.push l}
  | _ => pure ()

private unsafe def scalarCI (ci : ConstantInfo) : StateM ScalarState Unit := do
  scalarName ci.name
  ci.levelParams.forM scalarName
  scalarExpr ci.type
  if let some v := ci.value? true then scalarExpr v
  let family := match ci with
    | .defnInfo v => v.all
    | .thmInfo v => v.all
    | .opaqueInfo v => v.all
    | .inductInfo v => v.all ++ v.ctors
    | .ctorInfo v => [v.induct]
    | .recInfo v => v.all
    | _ => []
  family.forM scalarName
  if let .recInfo v := ci then
    for r in v.rules do scalarName r.ctor; scalarExpr r.rhs

private unsafe def scalarIRExpr (e : IR.Expr) : StateM ScalarState Unit := do
  match e with
  | .lit l =>
    if let .num _ := l then modify fun s => {s with irLiterals := s.irLiterals.push l}
  | .ctor i _ | .reuse _ i _ _ => scalarName i.name
  | .fap f _ | .pap f _ => scalarName f
  | _ => pure ()

private unsafe def scalarIRBody (b : IR.FnBody) : StateM ScalarState Unit := do
  if !(← fresh b) then return
  match b with
  | .vdecl _ _ e b => scalarIRExpr e; scalarIRBody b
  | .jdecl _ _ v b => scalarIRBody v; scalarIRBody b
  | .case tid _ _ cs =>
    scalarName tid
    for alt in cs do
      match alt with
      | .ctor info body => scalarName info.name; scalarIRBody body
      | .default body => scalarIRBody body
  | _ => if !b.isTerminal then scalarIRBody b.body

private unsafe def scalarIRDecl (d : IR.Decl) : StateM ScalarState Unit := do
  scalarName d.name
  if let .fdecl _ _ _ body info := d then
    scalarIRBody body
    if let some n := info.sorryDep? then scalarName n

-- These typed extension adapters correspond to the pinned registrations in
-- LCNF.PhaseExt/Specialize, DocString.Extension and Simp.SimpTheorems.
private unsafe def scalarFormat (f : Format) : StateM ScalarState Unit := do
  if !(← fresh f) then return
  match f with
  | .nest _ inner | .tag _ inner =>
    modify fun s => {s with formats := s.formats.push f}
    scalarFormat inner
  | .append a b => scalarFormat a; scalarFormat b
  | .group inner _ => scalarFormat inner
  | _ => pure ()

private unsafe def scalarDocCode (c : Doc.DocCode) : StateM ScalarState Unit := do
  for (_, highlight) in c.code do
    if let some h := highlight then
      match h with
      | .const n f | .field n f => scalarName n; scalarFormat f
      | .var n id f => scalarName n; scalarName id.name; scalarFormat f
      | .option n d => scalarName n; scalarName d
      | .literal n f => scalarName n; f.forM scalarFormat
      | _ => pure ()

private unsafe def scalarDynamic (d : Dynamic) : StateM ScalarState Unit := do
  scalarName d.typeName
  if let some v := d.get? Doc.Data.Local then
    scalarName v.name; scalarName v.fvarId.name; scalarExpr v.type
    v.lctx.forM fun decl => do
      scalarName decl.fvarId.name; scalarName decl.userName; scalarExpr decl.type
      decl.value?.forM scalarExpr
  if let some v := d.get? Doc.Data.LeanBlock then scalarDocCode v.commands
  if let some v := d.get? Doc.Data.LeanTerm then scalarDocCode v.term
  if let some v := d.get? Doc.Data.SetOption then scalarDocCode v.term

mutual
private unsafe def scalarInline (i : Doc.Inline ElabInline) : StateM ScalarState Unit := do
  if !(← fresh i) then return
  match i with
  | .emph xs | .bold xs | .link xs _ | .footnote _ xs | .concat xs => xs.forM scalarInline
  | .other c xs =>
    if let .custom d := c then scalarDynamic d
    xs.forM scalarInline
  | _ => pure ()
private unsafe def scalarBlock (b : Doc.Block ElabInline ElabBlock) : StateM ScalarState Unit := do
  if !(← fresh b) then return
  match b with
  | .para xs => xs.forM scalarInline
  | .ul xs | .ol _ xs => for x in xs do x.contents.forM scalarBlock
  | .dl xs => for x in xs do x.term.forM scalarInline; x.desc.forM scalarBlock
  | .blockquote xs | .concat xs => xs.forM scalarBlock
  | .other c xs =>
    if let .custom d := c then scalarDynamic d
    xs.forM scalarBlock
  | _ => pure ()
end
private unsafe def scalarPart (p : Doc.Part ElabInline ElabBlock Empty) : StateM ScalarState Unit := do
  if !(← fresh p) then return
  p.title.forM scalarInline
  p.content.forM scalarBlock
  p.subParts.forM scalarPart

private unsafe def scalarParam (p : Compiler.LCNF.Param .pure) : StateM ScalarState Unit := do
  scalarName p.fvarId.name; scalarName p.binderName; scalarExpr p.type
private unsafe def scalarArg (a : Compiler.LCNF.Arg .pure) : StateM ScalarState Unit := do
  match a with
  | .fvar id => scalarName id.name
  | .type e _ => scalarExpr e
  | _ => pure ()
private unsafe def scalarLCNFDecl (d : Compiler.LCNF.Decl .pure) : StateM ScalarState Unit := do
  scalarName d.name; d.levelParams.forM scalarName; scalarExpr d.type; d.params.forM scalarParam
  d.value.forCodeM fun code => code.forM fun c => do
    match c with
    | .let decl _ =>
      scalarName decl.fvarId.name; scalarName decl.binderName; scalarExpr decl.type
      match decl.value with
      | .lit l => if let .nat _ := l then modify fun s => {s with lcnfLiterals := s.lcnfLiterals.push l}
      | .proj n _ id _ => scalarName n; scalarName id.name
      | .const n us args _ => scalarName n; us.forM scalarLevel; args.forM scalarArg
      | .fvar id args => scalarName id.name; args.forM scalarArg
      | _ => pure ()
    | .fun decl _ _ | .jp decl _ =>
      scalarName decl.fvarId.name; scalarName decl.binderName; scalarExpr decl.type; decl.params.forM scalarParam
    | .cases cases =>
      scalarName cases.typeName; scalarExpr cases.resultType; scalarName cases.discr.name
      for a in cases.alts do
        if let .alt n ps _ _ := a then scalarName n; ps.forM scalarParam
    | .jmp id args => scalarName id.name; args.forM scalarArg
    | .return id => scalarName id.name
    | .unreach t => scalarExpr t
    | _ => pure ()
private unsafe def scalarSimp (e : Meta.SimpEntry) : StateM ScalarState Unit := do
  match e with
  | .thm t =>
    scalarExpr t.proof; t.levelParams.forM scalarName; scalarName t.origin.key
    for k in t.keys do
      match k with
      | .lit l => if let .natVal _ := l then modify fun s => {s with literals := s.literals.push l}
      | .const n _ | .proj n _ _ => scalarName n
      | .fvar id _ => scalarName id.name
      | _ => pure ()
  | .toUnfold n => scalarName n
  | .toUnfoldThms n ns => scalarName n; ns.forM scalarName

@[extern "matched_init_scalar_census"]
private unsafe opaque emitScalarCensus (roots : @& Array ModuleData)
  (names : @& Array Name) (literals : @& Array Literal)
  (irLiterals : @& Array IR.LitVal) (lcnfLiterals : @& Array Compiler.LCNF.LitValue)
  (formats : @& Array Format) (path : @& String) : IO Unit

unsafe def scalarCensus (roots : Array ModuleData) (path : String) : IO Unit := do
  let action : StateM ScalarState Unit := do
    for data in roots do
      for i in data.imports do scalarName i.module
      data.constNames.forM scalarName
      data.extraConstNames.forM scalarName
      data.constants.forM scalarCI
      for (n, entries) in data.entries do
        scalarName n
        -- Pinned IR.CompilerM exportIREntries explicitly erases Array IR.Decl
        -- to Array EnvExtensionEntry under this exact extension name.
        if n == ``IR.declMapExt then
          let decls : Array IR.Decl := unsafeCast entries
          decls.forM scalarIRDecl
        if n == ``Compiler.LCNF.baseExt || n == ``Compiler.LCNF.monoExt then
          let ds : Array (Compiler.LCNF.Decl .pure) := unsafeCast entries
          ds.forM scalarLCNFDecl
        if n == Name.str (Name.str (Name.str (Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str (Name.str .anonymous "_private") "Lean") "Compiler") "LCNF") "Specialize") 0) "Lean") "Compiler") "LCNF") "Specialize") "specCacheExt" then
          let es : Array Compiler.LCNF.Specialize.CacheEntry := unsafeCast entries
          for e in es do scalarExpr e.key; scalarName e.declName
        if n == ``versoDocStringExt then
          let ds : Array (Name × VersoDocString) := unsafeCast entries
          for (name, doc) in ds do
            scalarName name; doc.text.forM scalarBlock; doc.subsections.forM scalarPart
        if n == Name.str (Name.str (Name.num (Name.str (Name.str (Name.str (Name.str .anonymous "_private") "Lean") "DocString") "Extension") 0) "Lean") "versoModuleDocExt" then
          let ds : Array VersoModuleDocs.Snippet := unsafeCast entries
          for doc in ds do
            doc.text.forM scalarBlock
            for (_, _, p) in doc.sections do scalarPart p
        if n == ``Meta.simpExtension then
          let es : Array (ScopedEnvExtension.Entry Meta.SimpEntry) := unsafeCast entries
          for e in es do
            match e with
            | .global e => scalarSimp e
            | .scoped n e => scalarName n; scalarSimp e
  let (_, state) := action.run {}
  emitScalarCensus roots state.names state.literals state.irLiterals state.lcnfLiterals state.formats path

end MatchedInitProducer
