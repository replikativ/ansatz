import RuntimeCompileShim
import SourceModuleExport
import SourceModuleImport

open Lean Lean.IR

private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str", encodeName p, toJson s]
  | .num p n => Json.arr #[toJson "num", encodeName p, toJson (toString n)]

private def rowJson (row : RuntimeCompileShim.EvalConstWitnessIRRow) : Json :=
  Json.mkObj [("name", encodeName row.name), ("ir", toJson row.decl),
    ("sourceLocal", toJson row.sourceLocal), ("sourceModule", (row.sourceModule.map encodeName).getD Json.null)]

private def witnessJson (w : RuntimeCompileShim.EvalConstWitnessIR) : Json :=
  Json.mkObj [("schema", toJson w.schema), ("producer", toJson w.producer),
    ("leanCommit", toJson w.leanCommit),
    ("runtimeProfile", Json.mkObj [("wordBits", toJson w.wordBits), ("target", toJson w.target)]),
    ("name", encodeName w.name), ("boxedTarget", encodeName w.boxedTarget),
    ("declarations", Json.arr (w.rows.map rowJson)),
    ("missingDependencies", Json.arr (w.missingDependencies.map encodeName)),
    ("sorryDep", (w.sorryDep.map encodeName).getD Json.null)]

private def compile (env : Environment) (name : Name) (text : String) : IO Environment := do
  let input := Parser.mkInputContext text (name.toString ++ ".lean")
  let (header, pos, messages) ← Parser.parseHeader input
  unless !messages.hasErrors && Elab.HeaderSyntax.imports header == env.header.imports do
    throw <| IO.userError "IR witness oracle header mismatch"
  let state ← Elab.IO.processCommands input pos (Elab.Command.mkState (env.setMainModule name) messages {})
  if state.commandState.messages.hasErrors then
    for msg in state.commandState.messages.toList do IO.eprintln (← msg.toString)
    throw <| IO.userError "IR witness oracle compile failure"
  return state.commandState.env

private def parity (env : Environment) (name : Name) : IO Unit := do
  let old ← RuntimeCompileShim.exportEvalConstWitness env name
  let value ← RuntimeCompileShim.exportEvalConstWitnessIRLinear env name
  unless (witnessJson value).compress == old do
    throw <| IO.userError s!"Linear/string witness mismatch for {name}"
  IO.println <| (Json.mkObj [("case",toJson name.toString),("declarations",toJson value.rows.size),
    ("witness",witnessJson value)]).compress

private def terminal : FnBody := .ret .erased
private def call (name : Name) (next := terminal) : FnBody :=
  .vdecl ⟨7⟩ .object (.fap name #[]) next
private def pap (name : Name) (next := terminal) : FnBody :=
  .vdecl ⟨7⟩ .object (.pap name #[]) next
private def ci : CtorInfo := ⟨`ignoredCtorName, 0, 0, 0, 0⟩

private def assertDeps (label : String) (body : FnBody) (expected : Array Name) : IO Unit := do
  let (old, linear) := RuntimeCompileShim.bodyDepsLinearProbe body
  unless old == linear && linear == expected do
    throw <| IO.userError s!"Dependency/order/multiplicity mismatch: {label}"

private def dependencyOracle : IO Unit := do
  let shared := call `A
  assertDeps "vdecl pre-order" (call `A (pap `B (call `A))) #[`A,`B,`A]
  assertDeps "jdecl value before continuation" (.jdecl ⟨3⟩ #[] shared (pap `B)) #[`A,`B]
  let branch := FnBody.case `ignoredTypeName ⟨7⟩ .object #[
    .ctor ci shared, .ctor {ci with cidx := 1} (pap `B), .default shared]
  assertDeps "alternatives order and shared duplicate" branch #[`A,`B,`A]
  assertDeps "nested branch order" (call `Z (.jdecl ⟨3⟩ #[] branch (pap `C))) #[`Z,`A,`B,`A,`C]
  let expressions : Array IR.Expr := #[.ctor ci #[],.reset 0 ⟨7⟩,
    .reuse ⟨7⟩ ci false #[],.proj 0 ⟨7⟩,.uproj 0 ⟨7⟩,.sproj 0 0 ⟨7⟩,
    .fap `called #[],.pap `called #[],.ap ⟨7⟩ #[],.box .uint64 ⟨7⟩,
    .unbox ⟨7⟩,.lit (.num 0),.isShared ⟨7⟩]
  for i in [:expressions.size] do
    assertDeps s!"expression-{i}" (.vdecl ⟨7⟩ .object expressions[i]! terminal)
      (if i == 6 || i == 7 then #[`called] else #[])
  let wrappers := #[FnBody.set ⟨7⟩ 0 .erased shared, .setTag ⟨7⟩ 1 shared,
    .uset ⟨7⟩ 0 ⟨7⟩ shared, .sset ⟨7⟩ 0 0 ⟨7⟩ .uint8 shared,
    .inc ⟨7⟩ 1 false false shared, .dec ⟨7⟩ 1 false false shared, .del ⟨7⟩ shared]
  for i in [:wrappers.size] do assertDeps s!"continuation-{i}" wrappers[i]! #[`A]
  assertDeps "ret ignores variables" (.ret (.var ⟨7⟩)) #[]
  assertDeps "jmp terminal" (.jmp ⟨3⟩ #[.var ⟨7⟩,.erased]) #[]
  assertDeps "unreachable terminal" .unreachable #[]
  let mut dense := terminal
  let mut expected := #[]
  for i in [:2048] do dense := call (.num `dense i) dense
  for i in [:2048] do expected := expected.push (.num `dense (2047-i))
  assertDeps "dense depth2048" dense expected
  let mut emptyDeep := terminal
  for _ in [:4096] do emptyDeep := .vdecl ⟨7⟩ .object (.lit (.num 0)) emptyDeep
  assertDeps "empty depth4096" emptyDeep #[]
  let hugeName := Name.num (.str .anonymous "root.with.dot") (2^150+7)
  assertDeps "arbitrary numeric Name preserved" (call hugeName (pap hugeName)) #[hugeName,hugeName]
  IO.println "linear-body-dependencies: 30 cases passed (dense2048/empty4096)"

private unsafe def oracle : IO Unit := do
  dependencyOracle
  let mut env ← mkEmptyEnvironment
  for name in [`lcAny, `lcErased, `lcVoid] do
    env ← IO.ofExcept <| env.addDeclCore 1000000 1000
      (.axiomDecl {name, levelParams := [], type := mkSort (.succ .zero), isUnsafe := true}) none
      |>.mapError (fun _ => "marker admission failed")
  let a ← compile env `PreludeIdentity
    "prelude\n@[noinline] def left.{u} (α : Sort u) (x : α) : α := x\n@[noinline] def right.{u} (α : Sort u) (x : α) : α := x\n@[noinline] def answer.{u} (α : Sort u) (x : α) : α := left α (right α x)\n"
  parity a `answer
  parity a `missingLinearWitnessName
  let (data, _) ← SourceModuleExport.exportClassic a `PreludeIdentity
  let assembly := SourceModuleImport.assembleClassic data `PreludeIdentity "ansatz-source:linear-oracle"
  let imported ← SourceModuleImport.finalizeClassic assembly.state assembly.imports {}
  parity imported `answer
  let b ← compile imported `PreludeSecond
    "prelude\nimport PreludeIdentity\ndef second.{u} (α : Sort u) (x : α) : α := answer α x\n"
  parity b `second
  IO.println "linear-typed-witness-string-parity: 4 passed"

#eval oracle
