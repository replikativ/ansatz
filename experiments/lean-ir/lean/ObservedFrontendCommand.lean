/-
Adapted from Lean.Elab.Frontend.processCommand.
Copyright (c) 2019 Microsoft Corporation. Apache 2.0 license.
Original authors: Leonardo de Moura, Sebastian Ullrich.
-/
import Lean

/- A versioned observer companion for Lean 4.33.1, commit
   819816b2e0a3bf405af45ae5c7af2491d8f5bee6:Lean/Elab/Frontend.lean.
   This is NOT the original processCommand entry. The composition below keeps
   its parser/state/elaborator operations, adding a borrowed pre-elaboration
   policy boundary and an owned observation. No parsing or elaboration replay.
   The trusted host authenticates this source and admits the explicit gate;
   absence of that gate's reviewed policy must stop, never approve implicitly. -/
open Lean Lean.Elab Lean.Elab.Frontend

namespace ObservedFrontendCommand

/-- All inputs are borrowed actual parser occurrences. A successful BaseIO Unit
reply permits this one original elaboration. The host must retain any inputs
needed through a thrown elaboration and authenticate its own gate receipt.
This declaration supplies no implementation or native permission. -/
@[extern "ansatz_observed_frontend_gate_v1"]
opaque beforeElaboration
    (input : @& Parser.InputContext) (before : @& Frontend.State)
    (command : @& Syntax) (parsed : @& Parser.ModuleParserState)
    (messages : @& MessageLog) : BaseIO Unit

/-- Caller-owned observation, including the parser log before the original
elaborator resets messages. Field order is a versioned compiled layout contract.
Position fields are raw UTF-8 byte positions, not character indices. Booleans
are observations only; eoi plus exact captured end and both logs must be checked
by the host before a complete-file capability can be issued. -/
structure Observation where
  input : Parser.InputContext
  before : Frontend.State
  command : Syntax
  parsed : Parser.ModuleParserState
  parserMessages : MessageLog
  elaborationMessages : MessageLog
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  terminal : Bool
  eoi : Bool
  exit : Bool
  lateImport : Bool

/-- One parser call, a mandatory authenticated pre-elaboration boundary, then
one original elaborator call. A denied/unhandled gate leaves a paused invocation
and actual journal, not a successful command or rewindable parser transaction. -/
@[noinline] def processCommandObserved : FrontendM Observation := do
  let before ← get
  updateCmdPos
  let cmdState ← getCommandState
  let ictx ← getInputContext
  let pstate ← getParserState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts,
                 currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  match profileit "parsing" scope.opts fun _ =>
      Parser.parseCommand ictx pmctx pstate cmdState.messages with
  | (cmd, ps, messages) =>
    modify fun s => { s with commands := s.commands.push cmd }
    setParserState ps
    setMessages messages
    beforeElaboration ictx before cmd ps messages
    elabCommandAtFrontend cmd
    let after ← getCommandState
    return {
      input := ictx, before, command := cmd, parsed := ps,
      parserMessages := messages, elaborationMessages := after.messages,
      startPos := before.parserState.pos, endPos := ps.pos,
      terminal := Parser.isTerminalCommand cmd,
      eoi := cmd.isOfKind ``Parser.Command.eoi,
      exit := cmd.isOfKind ``Parser.Command.exit,
      lateImport := cmd.isOfKind ``Parser.Command.import }

end ObservedFrontendCommand
