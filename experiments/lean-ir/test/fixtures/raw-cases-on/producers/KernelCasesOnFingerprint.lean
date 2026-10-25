import Lean.Environment

namespace KernelCasesOnFingerprint
open Lean

private structure Scan where
  remaining : Nat := 100000
  mdata : Nat := 0
  letFalse : Nat := 0
  letTrue : Nat := 0
  rawMax : Nat := 0
  rawIMax : Nat := 0
  implicit : Nat := 0
  instImplicit : Nat := 0
  syntaxPayloads : Nat := 0
  markedBvarMask : Nat := 0

private abbrev ScanM := StateT Scan (Except String)

private def charge (depth : Nat) : ScanM Unit := do
  if depth > 256 then throw "RAW fixture profile depth bound"
  let state ← get
  if state.remaining == 0 then throw "RAW fixture profile work bound"
  set { state with remaining := state.remaining - 1 }

private partial def level (value : Level) (depth : Nat) : ScanM Unit := do
  charge depth
  match value with
  | .zero | .param _ => pure ()
  | .mvar _ => throw "Unexpected level metavariable in checked fixture"
  | .succ value => level value (depth + 1)
  | .max left right =>
    modify fun s => { s with rawMax := s.rawMax + 1 }
    level left (depth + 1)
    level right (depth + 1)
  | .imax left right =>
    modify fun s => { s with rawIMax := s.rawIMax + 1 }
    level left (depth + 1)
    level right (depth + 1)

private partial def expression (value : Expr) (depth : Nat) (marked : Bool) : ScanM Unit := do
  charge depth
  let child := fun value => expression value (depth + 1) marked
  match value with
  | .bvar index =>
    if marked then
      if index >= 64 then throw "Marked fixture variable exceeds fingerprint domain"
      modify fun s => { s with markedBvarMask := s.markedBvarMask ||| (2 ^ index) }
  | .fvar _ | .mvar _ => throw "Unexpected free/metavariable in checked fixture"
  | .sort value => level value (depth + 1)
  | .const _ levels =>
    for value in levels do level value (depth + 1)
  | .app function argument => child function; child argument
  | .lam _ type body info | .forallE _ type body info =>
    if info == .implicit then modify fun s => { s with implicit := s.implicit + 1 }
    if info == .instImplicit then modify fun s => { s with instImplicit := s.instImplicit + 1 }
    child type
    child body
  | .letE _ type value body nondep =>
    modify fun s => if nondep then { s with letTrue := s.letTrue + 1 }
      else { s with letFalse := s.letFalse + 1 }
    child type
    child value
    child body
  | .lit _ => pure ()
  | .mdata metadata body =>
    modify fun s => { s with mdata := s.mdata + 1 }
    if metadata.getString `oracle.marker != "preserve-this-payload" then
      throw "RAW fixture marker payload lost"
    for (_, entry) in metadata.entries do
      charge (depth + 1)
      match entry with
      | .ofSyntax payload =>
        match payload with
        | .node .none `oracle.payload #[.atom .none "opaque"] =>
          modify fun s => { s with syntaxPayloads := s.syntaxPayloads + 1 }
        | _ => throw "RAW fixture Syntax payload lost"
      | _ => pure ()
    expression body (depth + 1) true
  | .proj _ _ body => child body

/-- Independently inspect imported RAW nodes before constructor execution.
The finite vector is compared with the earlier native oracle's exact counters
and marked-variable SET (encoded as a bitmask), never a Java projection.
This fixture-specific observer neither checks nor admits a declaration. -/
@[noinline] def profileType (value : @& Expr) : Except String (Array Nat) := do
  let (_, state) ← (expression value 0 false).run {}
  return #[state.mdata, state.letFalse, state.letTrue, state.rawMax, state.rawIMax,
    state.implicit, state.instImplicit, state.syntaxPayloads, state.markedBvarMask]

end KernelCasesOnFingerprint
