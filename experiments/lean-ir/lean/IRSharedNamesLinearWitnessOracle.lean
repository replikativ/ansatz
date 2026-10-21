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
  let original ← RuntimeCompileShim.exportEvalConstWitness env name
  let typed ← RuntimeCompileShim.exportEvalConstWitnessIR env name
  let linear ← RuntimeCompileShim.exportEvalConstWitnessIRLinear env name
  let shared ← RuntimeCompileShim.exportEvalConstWitnessIRSharedNames env name
  let candidate ← RuntimeCompileShim.exportEvalConstWitnessIRSharedNamesLinear env name
  for (label, value) in #[("typed", typed), ("linear", linear),
                          ("shared", shared), ("shared-linear", candidate)] do
    unless (witnessJson value).compress == original do
      throw <| IO.userError s!"Exact witness mismatch: {label} / {name}"
  -- Deliberately no moduleNames field: identical ten-field typed envelope and
  -- reconstructed original JSON, including row ordering/sourceModule/duplicates.
  IO.println <| (Json.mkObj [("case", toJson name.toString),
    ("declarations", toJson candidate.rows.size), ("witness", witnessJson candidate)]).compress

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

namespace SharedNamesLinearOracle

/-- Guest-callable collector oracle. No frontend/imports/IO host operations.
case 0 dense straightline; 1 jdecl chains; 2 ordered case branches sharing body;
3 duplicate straightline names. Native main exercises the same code. -/
private def collectionInput (kind size : Nat) : IO (FnBody × Array Name) := do
  let mut body := terminal
  let mut expected : Array Name := #[]
  if kind == 0 || kind == 3 then
    for i in [:size] do body := call (.num `dense (if kind == 3 then i % 3 else i)) body
    for i in [:size] do expected := expected.push (.num `dense (if kind == 3 then (size-1-i) % 3 else size-1-i))
  else if kind == 1 then
    for i in [:size] do body := .jdecl ⟨3⟩ #[] (call (.num `join i)) body
    for i in [:size] do expected := expected.push (.num `join (size-1-i))
  else if kind == 2 then
    let shared := call `A (pap `B (call `A))
    let mut alternatives : Array Alt := #[]
    for i in [:size] do
      alternatives := alternatives.push (.ctor {ci with cidx := i} shared)
      expected := expected ++ #[`A, `B, `A]
    body := .case `ignoredTypeName ⟨7⟩ .object alternatives
  else throw <| IO.userError "Unsupported collector oracle kind"
  return (body, expected)

@[noinline] def collectionSummary (kind size : Nat) : IO Nat := do
  let (body, expected) ← collectionInput kind size
  let (old, linear) := RuntimeCompileShim.bodyDepsLinearProbe body
  unless old == expected && linear == expected do
    throw <| IO.userError "Collector order/multiplicity mismatch"
  return linear.size

/-- Isolated actual linear collector; does not invoke the quadratic oracle. -/
@[noinline] def collectionLinearSummary (kind size : Nat) : IO Nat := do
  let (body, expected) ← collectionInput kind size
  let linear := RuntimeCompileShim.bodyDepsLinearOnlyProbe body
  unless linear == expected do
    throw <| IO.userError "Linear collector order/multiplicity mismatch"
  return linear.size

/-- Original collector alone; parity oracle rather than a production entry. -/
@[noinline] def collectionOriginalSummary (kind size : Nat) : IO Nat := do
  let (body, expected) ← collectionInput kind size
  let original := RuntimeCompileShim.bodyDepsOriginalOnlyProbe body
  unless original == expected do
    throw <| IO.userError "Original collector order/multiplicity mismatch"
  return original.size

end SharedNamesLinearOracle

private unsafe def oracle : IO Unit := do
  dependencyOracle
  for kind in [:4] do
    for size in #[0, 1, 31, 256, 2048] do
      let actual ← SharedNamesLinearOracle.collectionSummary kind size
      let isolated ← SharedNamesLinearOracle.collectionLinearSummary kind size
      let isolatedOriginal ← SharedNamesLinearOracle.collectionOriginalSummary kind size
      unless actual == isolated && actual == isolatedOriginal do
        throw <| IO.userError "Isolated collectors differ"
      let expected := if kind == 2 then size * 3 else size
      unless actual == expected do throw <| IO.userError "Collector length mismatch"
  IO.println "shared-names-linear-adversarial-collector: 20 cases passed"
  let mut env ← mkEmptyEnvironment
  for name in [`lcAny, `lcErased, `lcVoid] do
    env ← IO.ofExcept <| env.addDeclCore 1000000 1000
      (.axiomDecl {name, levelParams := [], type := mkSort (.succ .zero), isUnsafe := true}) none
      |>.mapError (fun _ => "marker admission failed")
  let a ← compile env `PreludeIdentity
    "prelude\n@[noinline] def left.{u} (α : Sort u) (x : α) : α := x\n@[noinline] def right.{u} (α : Sort u) (x : α) : α := x\n@[noinline] def answer.{u} (α : Sort u) (x : α) : α := left α (right α x)\n"
  parity a `answer
  parity a `missingSharedNamesWitnessName
  let (data, _) ← SourceModuleExport.exportClassic a `PreludeIdentity
  let assembly := SourceModuleImport.assembleClassic data `PreludeIdentity "ansatz-source:shared-names-oracle"
  let imported ← SourceModuleImport.finalizeClassic assembly.state assembly.imports {}
  parity imported `answer
  let b ← compile imported `PreludeSecond
    "prelude\nimport PreludeIdentity\ndef second.{u} (α : Sort u) (x : α) : α := answer α x\n"
  parity b `second
  IO.println "shared-names-linear-exact-witness-parity: 4 cases x 4 typed variants passed"

#eval oracle
