import RuntimeCompileShim
import SourceModuleExport
import SourceModuleImport

open Lean

/- Native layout/parity oracle only. Load the freshly generated RuntimeCompileShim
   shared helper and native/GuestJsonTransport.cpp shared producer. Compaction
   attests scalar extents; the generic exporter never guesses heap padding. -/
@[extern "module_data_transport_export"]
private unsafe opaque exportDAG
  (roots : @& Array Json) (metadata : @& String) (path : @& String)
  (verify : Bool) : IO String

private def compile (env : Environment) (name : Name) (text : String) : IO Environment := do
  let input := Parser.mkInputContext text (name.toString ++ ".lean")
  let (header, pos, messages) ← Parser.parseHeader input
  unless !messages.hasErrors && Elab.HeaderSyntax.imports header == env.header.imports do
    throw <| IO.userError "Json witness oracle header mismatch"
  let state ← Elab.IO.processCommands input pos (Elab.Command.mkState (env.setMainModule name) messages {})
  if state.commandState.messages.hasErrors then
    for msg in state.commandState.messages.toList do IO.eprintln (← msg.toString)
    throw <| IO.userError "Json witness oracle compile failure"
  return state.commandState.env

private def parity (env : Environment) (name : Name) : IO Json := do
  let old ← RuntimeCompileShim.exportEvalConstWitness env name
  let value ← RuntimeCompileShim.exportEvalConstWitnessValue env name
  unless value.compress == old do throw <| IO.userError s!"Json/string witness mismatch for {name}"
  return value

private unsafe def oracle : IO Unit := do
  let mut env ← mkEmptyEnvironment
  for name in [`lcAny, `lcErased, `lcVoid] do
    env ← IO.ofExcept <| env.addDeclCore 1000000 1000
      (.axiomDecl {name, levelParams := [], type := mkSort (.succ .zero), isUnsafe := true}) none
      |>.mapError (fun _ => "marker admission failed")
  let a ← compile env `PreludeIdentity "prelude\n@[noinline] def answer.{u} (α : Sort u) (x : α) : α := x\n"
  let localWitness ← parity a `answer
  let missingWitness ← parity a `missingJsonWitnessName
  let (data, _) ← SourceModuleExport.exportClassic a `PreludeIdentity
  let assembled := SourceModuleImport.assembleClassic data `PreludeIdentity "ansatz-source:json-oracle"
  let imported ← SourceModuleImport.finalizeClassic assembled.state assembled.imports {}
  let importedWitness ← parity imported `answer
  let b ← compile imported `PreludeSecond
    "prelude\nimport PreludeIdentity\ndef second.{u} (α : Sort u) (x : α) : α := answer α x\n"
  let mixedWitness ← parity b `second
  let text := "λ" ++ String.singleton (Char.ofNat 0) ++ "😀\n\"\\"
  let shared := Json.mkObj [("nested", Json.arr #[Json.null, Json.bool true]), ("unicode", Json.str text)]
  let roots := #[Json.null, Json.bool false, Json.bool true,
    Json.num ⟨0, 0⟩, Json.num ⟨-1, 0⟩,
    Json.num ⟨(2^160 + 1 : Nat), 0⟩, Json.num ⟨-(2^161 + 1 : Int), 0⟩,
    Json.num ⟨-125, 2⟩, Json.num ⟨100, 2⟩,
    Json.str text, Json.arr #[], Json.obj {}, shared, shared,
    localWitness, missingWitness, importedWitness, mixedWitness]
  let nativeFile : System.FilePath := "target/witness-json-value/guest-json.native-v2"
  let _ ← CompactedRegion.save nativeFile `GuestJsonWitnessOracle roots #[] none
  let (compacted, _) ← CompactedRegion.read (α := Array Json) nativeFile #[]
  let metadata := Json.mkObj [("leanVersion", toJson Lean.versionString), ("leanCommit", toJson Lean.githash),
    ("nativeEnvironmentFinalized", toJson false), ("regionAddressesTransported", toJson false),
    ("modules", Json.arr #[]), ("oracle", toJson "GuestJsonWitnessOracle"),
    ("expected", Json.arr roots), ("parityCases", toJson #["local", "missing", "imported", "mixed"])]
  IO.FS.writeFile "target/witness-json-value/guest-json.expected.json" (Json.arr roots).compress
  IO.println (← exportDAG compacted metadata.compress "target/witness-json-value/guest-json.jsonl" true)
  IO.println "guest-json-witness-string-parity: 4 passed"

#eval oracle
