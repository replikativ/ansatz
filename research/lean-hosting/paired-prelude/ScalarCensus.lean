import Lean
open Lean
namespace MatchedPreludeProducer

private structure ScalarState where
  seen : Std.HashSet USize := {}
  names : Array Name := #[]
  literals : Array Literal := #[]
  irLiterals : Array IR.LitVal := #[]

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
  | .mvar _ => pure ()

private unsafe def scalarExpr (e : Expr) : StateM ScalarState Unit := do
  if !(← fresh e) then return
  match e with
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

@[extern "matched_prelude_scalar_census"]
private unsafe opaque emitScalarCensus (roots : @& Array ModuleData)
  (names : @& Array Name) (literals : @& Array Literal)
  (irLiterals : @& Array IR.LitVal) (path : @& String) : IO Unit

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
  let (_, state) := action.run {}
  emitScalarCensus roots state.names state.literals state.irLiterals path

end MatchedPreludeProducer
