# Demand-loaded Java executable code

Implementation plan, 2026-10-29. This document separates the next runtime steps
from capabilities already implemented in [program generations](JAVA_PROGRAM_GENERATIONS.md).
Only the prepared-body separation is implemented in the current tranche.
Header registration, code requests, prepared-global import and frontend execution
on Java remain subsequent acceptance gates.

## Why separate identity from implementation

The authenticated saved frontend globals have a bounded heap-field closure:
47,240 objects, including 11,914 closures targeting 2,412 distinct exact Lean
Names. A metadata-only expansion of their static code dependencies stopped at
64 MiB with 14,943 declarations selected and 7,872 unique Names still pending.
These are serialized-data counts, not Java heap or execution measurements.
Importing an unused callback must not force its transitive executable closure.

Keep each Function's identity and ABI separate from its prepared body and stack
layout. Program slots own immutable `PreparedBody {body, width, joinWidth}`
records. Descendants inherit prepared slots unchanged; siblings can prepare an
unforced slot independently against their own exact dependency identities.
Do not cache linked bodies globally by Name or original row hash: sibling
dependencies can have different numeric IDs and Function objects.

The initial refactor preserves eager preparation, public calls and both drivers.
It grants no new loading capability. Parsing/layout builders must remain local;
published body/layout records and inherited Function descriptors are not mutated.
Private runtime stream descriptors need an explicit intrinsic path; they must
not index ordinary Program slots with their synthetic IDs.

The [bounded implementation record](../measurements/java-ir-prepared-bodies-2026-10-29.edn)
passes 17 generation tests / 145 assertions and the combined isolated jar gate
of 339 test executions / 13,376 assertions in a 384 MiB JVM. Continuations and forks
preserve exact active/saved prepared-layout identities. A paired warmed RBMap
control retained equal allocation near 1.516 MB per run; explicit CPU medians
were prior 2.452 ms / split 2.452 ms, recursive 2.025 / 2.074 ms. These are shared
machine controls, not a native comparison or a performance improvement claim.

## Header and source authority

The next tranche needs an immutable accepted catalogue binding: exact structured
Lean Name to original declaration identity, including the accepted source cohort
and overlay resolution. A header captures declaration kind, parameter IDs/types,
borrow bits, result type and explicit initialized-global classification. A caller
supplying a hash string does not authenticate a header or its original bytes.
The trusted adapter must verify bytes and extraction against its accepted source.
The engine must preserve and check that adapter's actual binding identities.

Register headers append-only without executing code or retaining caller-owned
mutable rows. Original static calls and PAP targets resolve through the same
accepted catalogue. Unknown or conflicting Names reject; initialized-global
metadata comes from the authentic source, not a heuristic over unreachable bodies.
Known unsupported scalar types may be admitted as metadata only, with named
execution rejection. They must never silently become object lanes.

Materialization prepares one selected body's layout against registered dependency
headers, producing an immutable descendant. It does not recursively prepare those
dependencies. Once prepared, a slot cannot be replaced. Failure publishes nothing.
Preserve inherited header identity, ABI and prepared-slot identity. The existing
eager `prepare` and `extend` APIs remain useful convenience operations over this
model.

## Code demand and control

Use a distinct `CodeRequest`, separate from `HostRequest` and guest extern results.
The explicit driver suspends before entering an unprepared body, with a committed
activation containing target identity, accepted source identity, arguments,
return destination/kind, continuation and any AP surplus. No callee instruction
or initializer has run. `advance` at a code request returns without polling.
The recursive driver may explicitly reject unprepared execution; it must not
invoke a hidden loader or fall back to another interpreter.

Root arguments transfer once after entry validation. Static FAP borrowed arguments
do not gain owner credits merely because a request stores their views. AP may
consume its closure and transfer captures before suspension only if the committed
activation records that disposition. A code reply must enter the prepared target
without repeating AP preparation or the facade's borrowed-argument adaptation.
PAP construction needs only a supported authentic ABI, not a body.

Completion validates the exact pending request, actual descendant lineage,
requested header identity, prepared target and ABI before claiming the request.
Allocate replacement engine tables before publication. Wrong, stale, foreign or
duplicate completion leaves the request and current Program unchanged. Once
claimed, an activation failure becomes terminal; it cannot replay transferred
ownership. Loader failure is explicit and branch-local, with bounded diagnostics.
Bound source fetch and preparation independently from guest instruction fuel.

Installation may occur at idle, host requests and committed code requests. Active
caller bodies and frame layouts remain valid. A continuation restores its saved
caller layout; it does not resolve that layout again through a new header.
Fork requests, activation arguments, AP surplus, heap and constants through the
same graph memo. Child request identities belong to the child engine. Siblings
can resolve code independently without sharing mutable control or code slots.

Readiness precedes body forcing. A ready nullary cached value requires no body.
An explicitly initialized global without an installed ready value raises a
distinct unavailable-global error. It must not demand its genuine sentinel
`unreachable` body or rerun initialization.

## Acceptance sequence

1. Preserve eager behavior while moving layout into Program slots. Exercise both
   drivers, self tail calls, host suspension, forks and inherited generations.
2. Register two small original captured headers; demand an unprepared root, prepare
   its body and resume to its original result in the retained small REPL.
3. Exercise nested FAP, PAP without forcing, AP/overapplication, scalar returns,
   ready nullaries, missing initialized globals and unsupported lanes. Fork a
   pending request and link siblings with different dependency-ID assignments.
   Cover rejected source/header/ABI bindings, partial preparation and duplicate
   replies without state changes.
4. Import the actual saved `ppExt` descriptor, its `mkInitial` closure and captured
   ref. Register authentic headers without eagerly preparing their code closure.
   Execute demanded bodies and test forked ref mutation isolation. Measure actual
   reached code/globals and conversion cost before widening this slice.
5. Restore the intact registry and execute the original header parser. Real
   `parseHeader` constructs an empty environment by running all 219 registered
   `mkInitial` callbacks in this companion; a fabricated reduced environment is
   not equivalent. Then connect matching lazy kernel stores and genuine imported
   frontend state to elaborate, admit and execute `def answer : Nat := 42`.

The prepared graph importer remains separate. RC-zero refs are mutable persistent
objects and must be copied per fork. Positive RC counts from a whole checkpoint
cannot be copied blindly into a selected graph: establish explicit root/field
ownership or a justified owner envelope before publishing it. Drop temporary
source-ID construction tables when no longer needed. Native resources and tasks
require their own supported contracts.

## Reference and limits

Lean reference: pinned `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
`src/library/ir_interpreter.cpp` (load, lookup and call),
`src/Lean/Parser/Module.lean` (`parseHeader`) and
`src/Lean/Environment.lean` (`mkEmptyEnvironment`, extension initialization).
Prepared kernel-store loading already remains lazy; this plan does not require
proof replay or eager restoration of the legacy frontend image.

This is a route to bounded frontend experiments, not evidence of Java frontend
self-hosting, full Lean runtime coverage, or native-competitive performance.
Future Pattern/JVM compilation can target the same values, generation identities,
prepared slots and explicit control boundaries. LLVM is not required.
