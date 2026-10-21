import RuntimeCompileShim

open Lean Lean.IR

private def terminal : FnBody := .ret .erased
private def call (name : Name) (next := terminal) : FnBody :=
  .vdecl ⟨7⟩ .object (.fap name #[]) next
private def pap (name : Name) (next := terminal) : FnBody :=
  .vdecl ⟨7⟩ .object (.pap name #[]) next
private def ci : CtorInfo := ⟨`ignoredCtorName, 0, 0, 0, 0⟩


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
