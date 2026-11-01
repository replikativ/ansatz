import Lean.Elab.Frontend

namespace HostedFrontendProbe

/-- Creates a guest-owned environment after imported module initialization.
No native environment pointer or imported .olean environment is supplied. -/
@[noinline] def emptyEnvironmentSummary : IO Nat := do
  let env ← Lean.mkEmptyEnvironment
  return if env.contains `HostedSort then 1 else 0

/-- Exercise Lean.Elab.process itself, including its incremental command/task
pipeline. Inputs are command bodies: this entry does not process an import header.
The result observes both the diagnostics and declarations in the returned env. -/
@[noinline] def processSummary (text : String) : IO Nat := do
  let env ← Lean.mkEmptyEnvironment
  let (env, messages) ← Lean.Elab.process text env {} (some "HostedFrontendProbe.input")
  return (if messages.hasErrors then 1 else 0) +
    (if env.contains `HostedSort then 10 else 0) +
    (if env.contains `hostedValue then 100 else 0) +
    (if env.contains `answer then 1000 else 0)

def cases : List (String × String) := [
  ("empty", ""),
  ("namespace", "namespace Hosted\nend Hosted\n"),
  ("sort-axiom", "axiom HostedSort : Sort 1\n"),
  ("dependent-axiom", "axiom HostedSort : Sort 1\naxiom hostedValue : HostedSort\n"),
  ("bad-type", "set_option autoImplicit false\naxiom hostedValue : UnknownType\n"),
  ("identity-definition", "def answer.{u} (α : Sort u) (x : α) : α := x\n")]

/-- Smaller gate using the original synchronous FrontendM command loop from
Frontend.lean, not the newer IO.processCommandsIncrementally wrapper. -/
@[noinline] def synchronousProcessSummary (text : String) : IO Nat := do
  let env ← Lean.mkEmptyEnvironment
  let inputCtx := Lean.Parser.mkInputContext text "HostedFrontendProbe.input"
  let (_, state) ← (Lean.Elab.Frontend.processCommands { inputCtx }).run {
    commandState := Lean.Elab.Command.mkState env {} {}
    parserState := {}
    cmdPos := 0
  }
  return (if state.commandState.messages.hasErrors then 1 else 0) +
    (if state.commandState.env.contains `HostedSort then 10 else 0) +
    (if state.commandState.env.contains `hostedValue then 100 else 0) +
    (if state.commandState.env.contains `answer then 1000 else 0)

/-- End-to-end target after the observation probes: elaborate a fresh closed
polymorphic definition, obtain its compiled value, and apply it. This unseeded negative probe is expected to report the compiler marker
`lcAny` missing; declaration presence alone is not executable success. -/
@[noinline] unsafe def elaborateAndRunIdentity (value : Nat) : IO Nat := do
  let env ← Lean.mkEmptyEnvironment
  let (env, messages) ← Lean.Elab.process
    "def answer.{u} (α : Sort u) (x : α) : α := x\n" env {}
  if messages.hasErrors then
    throw <| IO.userError "identity elaboration reported errors"
  -- The erased type argument still occupies a runtime slot. Unit supplies
  -- that ignored slot without requiring a higher-universe evalConst type.
  let answer ← IO.ofExcept <| env.evalConst (Unit → Nat → Nat) {} `answer (checkMeta := false)
  return answer () value

/-- Exact compiler-marker declarations from pinned Init.Prelude, admitted through
normal strict kernel checking. This explicit three-axiom bootstrap is a smaller
experiment than importing Init; it does not replace the eventual import layer. -/
@[noinline] def compilerMarkerEnvironment : IO Lean.Environment := do
  let mut env ← Lean.mkEmptyEnvironment
  for name in [`lcAny, `lcErased, `lcVoid] do
    env ← IO.ofExcept <| env.addDeclCore 1000000 1000
      (.axiomDecl {name, levelParams := [], type := Lean.mkSort (.succ .zero), isUnsafe := true}) none
      |>.mapError (fun _ => "compiler marker admission failed")
  return env

/-- Positive end-to-end target with the explicit minimal compiler bootstrap. -/
@[noinline] unsafe def elaborateAndRunSeededIdentity (value : Nat) : IO Nat := do
  let env ← compilerMarkerEnvironment
  let (env, messages) ← Lean.Elab.process
    "def answer.{u} (α : Sort u) (x : α) : α := x\n" env {}
  if messages.hasErrors then
    throw <| IO.userError "seeded identity elaboration reported errors"
  let answer ← IO.ofExcept <| env.evalConst (Unit → Nat → Nat) {} `answer (checkMeta := false)
  return answer () value

end HostedFrontendProbe

unsafe def main : IO Unit := do
  IO.println s!"empty-environment\t{← HostedFrontendProbe.emptyEnvironmentSummary}"
  for (label, text) in HostedFrontendProbe.cases do
    IO.println s!"incremental/{label}\t{← HostedFrontendProbe.processSummary text}"
    IO.println s!"synchronous/{label}\t{← HostedFrontendProbe.synchronousProcessSummary text}"

  try
    IO.println s!"unseeded-identity-call\t{← HostedFrontendProbe.elaborateAndRunIdentity 42}"
  catch _ =>
    IO.println "unseeded-identity-call\tblocked-as-expected"
  IO.println s!"seeded-identity-call\t{← HostedFrontendProbe.elaborateAndRunSeededIdentity 42}"
