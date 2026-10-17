import RuntimeCompileShim
import SourceModuleExport
import SourceModuleImport

open Lean Lean.IR

@[extern "module_data_transport_export"]
private unsafe opaque exportDAG
  (roots : @& Array IR.Decl) (metadata : @& String) (path : @& String)
  (verify : Bool) : IO String

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

private def unusualName : Name := .str (.num (.str .anonymous "root.with.dot") (2^130+7)) ""
private def v : VarId := ⟨7⟩
private def bigV : VarId := ⟨2^100+9⟩
private def j : JoinPointId := ⟨3⟩
private def ci : CtorInfo := ⟨unusualName, 123, 3, 1, 25⟩
private def args : Array Arg := #[.var v, .erased, .var bigV]
private def types : Array IRType := #[.float,.uint8,.uint16,.uint32,.uint64,.usize,
  .erased,.object,.tobject,.float32,.struct none #[.object,.uint8],
  .union unusualName #[.float,.uint64],.tagged,.void,
  .struct (some unusualName) #[.struct none #[], .union .anonymous #[]]]
private def expressions : Array IR.Expr := #[.ctor ci args,.reset 3 v,
  .reuse v ci false args,.proj 2 v,.uproj 1 v,.sproj 3 17 v,
  .fap unusualName args,.pap unusualName args,.ap v args,.box .uint64 v,
  .unbox v,.lit (.num (2^150+1)),.isShared v,
  .reuse v ci true args,.lit (.str "λ\n\"\\"),.lit (.num 0)]
private def params : Array Param := types.mapIdx fun i type => ⟨⟨i⟩, i % 2 == 0, type⟩
private def terminal : FnBody := .ret .erased
private def bodies : Array FnBody := #[
  .vdecl v .object (.ctor ci args) terminal,
  .jdecl j params terminal terminal,
  .set v 2 .erased terminal,
  .setTag v 111 terminal,
  .uset v 1 bigV terminal,
  .sset v 3 17 bigV .uint32 terminal,
  .inc v 2 false false terminal,
  .dec v 3 false false terminal,
  .del v terminal,
  .case unusualName v .object #[.ctor ci terminal,.default terminal],
  .ret (.var bigV),.jmp j args,.unreachable]

private def declarations : Array IR.Decl := Id.run do
  let mut result := #[]
  for expr in expressions do
    result := result.push <| .fdecl unusualName params .object (.vdecl v .object expr terminal) {}
  for body in bodies do
    result := result.push <| .fdecl unusualName params .void body {sorryDep? := some unusualName}
  for c in [false,true] do
    for persistent in [false,true] do
      result := result.push <| .fdecl unusualName #[] .object (.inc v 5 c persistent (.dec v 7 c persistent terminal)) {}
  for type in types do
    result := result.push <| .fdecl unusualName #[] type terminal {}
  for entry in [ExternEntry.adhoc unusualName, .inline unusualName "#1 + #2", .standard unusualName "host_λ", .opaque] do
    result := result.push <| .extern unusualName params .object {entries := [entry]}
  result := result.push <| .extern .anonymous #[] .erased {entries := []}
  result := result.push <| .extern unusualName params .void {
    entries := [.adhoc .anonymous, .inline unusualName "#1", .standard unusualName "f", .opaque]}
  return result

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

private def parity (env : Environment) (name : Name) : IO RuntimeCompileShim.EvalConstWitnessIR := do
  let old ← RuntimeCompileShim.exportEvalConstWitness env name
  let value ← RuntimeCompileShim.exportEvalConstWitnessIR env name
  unless (witnessJson value).compress == old do
    throw <| IO.userError s!"Typed/string witness mismatch for {name}"
  return value

private unsafe def oracle : IO Unit := do
  let mut env ← mkEmptyEnvironment
  for name in [`lcAny, `lcErased, `lcVoid] do
    env ← IO.ofExcept <| env.addDeclCore 1000000 1000
      (.axiomDecl {name, levelParams := [], type := mkSort (.succ .zero), isUnsafe := true}) none
      |>.mapError (fun _ => "marker admission failed")
  let a ← compile env `PreludeIdentity "prelude\n@[noinline] def answer.{u} (α : Sort u) (x : α) : α := x\n"
  let localWitness ← parity a `answer
  let missingWitness ← parity a `missingIRWitnessName
  let (data, _) ← SourceModuleExport.exportClassic a `PreludeIdentity
  let assembled := SourceModuleImport.assembleClassic data `PreludeIdentity "ansatz-source:ir-oracle"
  let imported ← SourceModuleImport.finalizeClassic assembled.state assembled.imports {}
  let importedWitness ← parity imported `answer
  let b ← compile imported `PreludeSecond
    "prelude\nimport PreludeIdentity\ndef second.{u} (α : Sort u) (x : α) : α := answer α x\n"
  let mixedWitness ← parity b `second
  let witnesses := #[localWitness,missingWitness,importedWitness,mixedWitness]
  let roots := declarations
  let nativeFile : System.FilePath := "target/witness-ir-value/ir-value.native-v2"
  let _ ← CompactedRegion.save nativeFile `IRValueWitnessOracle roots #[] none
  let (compacted, _) ← CompactedRegion.read (α := Array IR.Decl) nativeFile #[]
  let metadata := Json.mkObj [("leanVersion",toJson Lean.versionString),("leanCommit",toJson Lean.githash),
    ("nativeEnvironmentFinalized",toJson false),("regionAddressesTransported",toJson false),
    ("modules",Json.arr #[]),("oracle",toJson "IRValueWitnessOracle"),("expected",toJson roots)]
  IO.FS.writeFile "target/witness-ir-value/ir-value.expected.json" (toJson roots).compress
  IO.println (← exportDAG compacted metadata.compress "target/witness-ir-value/ir-value.jsonl" true)
  let witnessFile : System.FilePath := "target/witness-ir-value/witness-value.native-v2"
  let _ ← CompactedRegion.save witnessFile `IRValueWitnessOracleWitness witnesses #[] none
  let (witnesses, _) ← CompactedRegion.read (α := Array RuntimeCompileShim.EvalConstWitnessIR) witnessFile #[]
  let expected := Json.arr (witnesses.map witnessJson)
  IO.FS.writeFile "target/witness-ir-value/witness-value.expected.json" expected.compress
  let metadata := metadata.setObjVal! "expected" expected
  IO.println (← exportDAG (unsafeCast witnesses) metadata.compress "target/witness-ir-value/witness-value.jsonl" true)
  let mut deepBody := terminal
  for i in [:4096] do
    deepBody := .vdecl v .object (.lit (.num i)) deepBody
  let deepDecl := IR.Decl.fdecl unusualName #[] .object deepBody {}
  -- Include original native ToJson as a separate object DAG root, avoiding a
  -- deeply recursive JSON text parser in the host test or manifest reader.
  let deepJson := toJson deepDecl
  let deepRoots : Array IR.Decl := #[deepDecl, unsafeCast deepJson]
  let deepFile : System.FilePath := "target/witness-ir-value/deep-value.native-v2"
  let _ ← CompactedRegion.save deepFile `IRValueWitnessOracleDeep deepRoots #[] none
  let (deepRoots, _) ← CompactedRegion.read (α := Array IR.Decl) deepFile #[]
  let deepMetadata := (metadata.setObjVal! "expected" Json.null).setObjVal! "depth" (toJson (4096 : Nat))
  IO.println (← exportDAG deepRoots deepMetadata.compress "target/witness-ir-value/deep-value.jsonl" true)
  IO.println "typed-ir-witness-string-parity: 4 passed"

#eval oracle
