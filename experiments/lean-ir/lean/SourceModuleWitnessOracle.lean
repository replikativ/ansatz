import SourceModuleImport
import SourceModuleExport
import RuntimeCompileShim

open Lean

/- Reproduce from experiments/lean-ir using the pinned4.33.1 toolchain.
   First compile SourceModuleExport/SourceModuleImport to target/*.olean if absent.
   mkdir -p target/source-module-witness
   LEAN_NUM_THREADS=1 lean +leanprover/lean4:v4.33.1 \
     -o target/source-module-witness/RuntimeCompileShim.olean \
     -c target/source-module-witness/RuntimeCompileShim.c lean/RuntimeCompileShim.lean
   leanir_sysroot="$(lean +leanprover/lean4:v4.33.1 --print-prefix)"
   cc -O0 -shared -fPIC -I "$leanir_sysroot/include" \
     target/source-module-witness/RuntimeCompileShim.c \
     -L "$leanir_sysroot/lib/lean" -lleanshared -Wl,-rpath,"$leanir_sysroot/lib/lean" \
     -o target/source-module-witness/libRuntimeCompileShimWitness.so
   LEAN_PATH=target/source-module-witness:target LEAN_NUM_THREADS=1 \
     lean +leanprover/lean4:v4.33.1 \
     --load-dynlib=target/source-module-witness/libRuntimeCompileShimWitness.so \
     lean/SourceModuleWitnessOracle.lean
   The PIC helper provides the private extern wrappers for the native interpreter.
   #eval avoids invoking RuntimeCompileShim's separately imported global main.
-/

private def compile (env : Environment) (name : Name) (text : String) : IO Environment := do
  let input := Parser.mkInputContext text (name.toString ++ ".lean")
  let (header, pos, messages) ← Parser.parseHeader input
  unless !messages.hasErrors && Elab.HeaderSyntax.imports header == env.header.imports do
    throw <| IO.userError "source oracle header mismatch"
  let state ← Elab.IO.processCommands input pos
    (Elab.Command.mkState (env.setMainModule name) messages {})
  if state.commandState.messages.hasErrors then
    for msg in state.commandState.messages.toList do IO.eprintln (← msg.toString)
    throw <| IO.userError "source oracle compilation failed"
  return state.commandState.env

private def encodeName : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str",encodeName p,toJson s]
  | .num p n => Json.arr #[toJson "num",encodeName p,toJson (toString n)]
private def assertWitness (env : Environment) (name : Name) (localOnly : Bool) : IO Unit := do
  let witness ← RuntimeCompileShim.exportEvalConstWitness env name
  let json ← IO.ofExcept <| Json.parse witness
  let rows ← IO.ofExcept <| json.getObjValAs? (Array Json) "declarations"
  let mut hasAnswer := false
  let mut hasAnswerBoxed := false
  let mut hasLocal := false
  let mut hasImportedReduced := false
  for row in rows do
    let rowName ← IO.ofExcept <| row.getObjVal? "name"
    let sourceLocal ← IO.ofExcept <| row.getObjValAs? Bool "sourceLocal"
    let source ← IO.ofExcept <| row.getObjVal? "sourceModule"
    if sourceLocal then
      unless source == Json.null do throw <| IO.userError "local sourceModule must be null"
      hasLocal := true
    else
      unless source == encodeName `PreludeIdentity do
        throw <| IO.userError "imported sourceModule must be PreludeIdentity"
    if rowName == encodeName `answer then hasAnswer := true
    if rowName == encodeName `answer._boxed then hasAnswerBoxed := true
    if rowName == encodeName `answer._redArg && !sourceLocal then hasImportedReduced := true
    if localOnly && !sourceLocal then throw <| IO.userError "source-local witness unexpectedly imported"
  if name == `answer then
    unless hasAnswer do throw <| IO.userError "witness omitted answer dependency"
    unless hasAnswerBoxed do throw <| IO.userError "witness omitted boxed answer"
  if localOnly || name == `second then
    unless hasLocal do throw <| IO.userError "witness omitted local declarations"
  if name == `second then
    unless hasImportedReduced do throw <| IO.userError "B witness omitted imported A dependency"
  IO.println <| (Json.mkObj [("case",toJson (if localOnly then "local-answer" else name.toString)),
    ("mainModule",encodeName env.mainModule), ("witness",json)]).compress

private unsafe def witnessOracle : IO Unit := do
  let mut env ← mkEmptyEnvironment
  for name in [`lcAny, `lcErased, `lcVoid] do
    env ← IO.ofExcept <| env.addDeclCore 1000000 1000
      (.axiomDecl {name, levelParams := [], type := mkSort (.succ .zero), isUnsafe := true}) none
      |>.mapError (fun _ => "marker admission failed")
  let a ← compile env `PreludeIdentity "prelude\n@[noinline] def answer.{u} (α : Sort u) (x : α) : α := x\n"
  assertWitness a `answer true
  let (data, _) ← SourceModuleExport.exportClassic a `PreludeIdentity
  unless data.constants.size == 4 && data.imports.isEmpty do
    throw <| IO.userError "source oracle expected four constants and no imports"
  let assembly := SourceModuleImport.assembleClassic data `PreludeIdentity "ansatz-source:native-oracle"
  -- This path does not serialize or mmap anything and must never call native
  -- CompactedRegion.free on its logical region. Ordinary Lean refs own the data.
  let imported ← SourceModuleImport.finalizeClassic assembly.state assembly.imports {}
  unless imported.header.imports == #[{module := `PreludeIdentity}] &&
      imported.toKernelEnv.quotInit && (imported.getModuleIdxFor? `answer).map ModuleIdx.toNat == some 0 do
    throw <| IO.userError "real source finalizer header/provenance mismatch"
  assertWitness imported `answer false
  let b ← compile imported `PreludeSecond
    "prelude\nimport PreludeIdentity\ndef second.{u} (α : Sort u) (x : α) : α := answer α x\n"
  assertWitness b `answer false
  assertWitness b `second false
  let second ← IO.ofExcept <| b.evalConst (Unit → Nat → Nat) {} `second (checkMeta := false)
  unless second () 42 == 42 do throw <| IO.userError "source A→B result mismatch"
  IO.println (SourceModuleImport.finalizerHeader imported)
  IO.println "source-owned-module-A-to-B: 42"

#eval witnessOracle
