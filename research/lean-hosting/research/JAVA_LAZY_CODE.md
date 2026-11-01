# Demand-loaded Java executable code

Implementation plan, 2026-10-29. This document separates the next runtime steps
from capabilities already implemented in [program generations](JAVA_PROGRAM_GENERATIONS.md).
Prepared-body separation, header registration and explicit selected-body
materialization and forkable code requests are implemented. A narrow persistent
graph/global bootstrap importer is implemented; wider positive-RC import and
frontend execution on Java remain subsequent acceptance gates.

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

Header admission uses an immutable accepted catalogue binding: exact structured
Lean Name to original declaration identity, including the accepted source cohort
and overlay resolution. A header captures declaration kind, parameter IDs/types,
borrow bits, result type and explicit initialized-global classification. A caller
supplying a hash string does not authenticate a header or its original bytes.
The trusted adapter must verify bytes and extraction against its accepted source.
The engine must preserve and check that adapter's actual binding identities.

`SourceBinding(acceptedCatalogueSnapshot)` retains a lightweight trusted-adapter
authority/lease token, not parsed catalogue contents. Its `header(row, sha256)`
issues an opaque immutable Header, ignoring the body while capturing original
Name, parameter IDs/raw types/borrow flags, result and runtime/source metadata.
This does not check a supplied digest against raw bytes. The adapter must pin its
source, authenticate bytes and check extraction before issuing a header.

`Program.registerHeaders(base, headers[, additionalExterns])` admits descriptors
without bodies. `Program.materialize(base, target, originalRow, directHeaders)`
transactionally prepares exactly one original fdecl body. Direct headers must be
the exact unique non-self FAP/PAP targets from the same SourceBinding; missing,
extra, foreign and conflicting descriptors reject. Existing slots cannot be
replaced. Host extern ABIs must be registered before or with their headers;
already-published unavailable externs cannot be rebound in this tranche.

Known unsupported numeric lanes remain metadata and reject execution explicitly.
Structured types and inline/other-backend extern descriptions are not covered.
PAP construction can reference an unforced supported boxed target. The recursive
driver rejects missing code before taking root/AP inputs; the explicit driver
commits a CodeRequest activation instead. A failed active guest frame still has
the existing unsupported general-cleanup limitation.

The [header implementation record](../measurements/java-ir-executable-headers-2026-10-29.edn)
passes 10 focused tests / 62 assertions and the combined isolated jar gate of
349 test executions / 13,438 assertions at 384 MiB. Independent review found and
fixed a static-extern initialized-global readiness bypass and inconsistent inner
declaration Names. New gates cover those paths and AP capture/closure ownership.
Paired RBMap allocation remained unchanged; CPU medians were recursive prior
2.434 ms / headers 2.437 ms and explicit 3.005 / 3.036 ms. No speedup is claimed.

The retained 384 MiB REPL admitted all 2,412 actual captured closure header
capsules with zero bodies prepared. In one observation, capsule parsing took
32.9 ms caller CPU / 48.8 MB cumulative allocation, and header construction plus
registration took 52.1 ms / 59.7 MB cumulative allocation. These are allocation
totals, not retained heap estimates; the capsules are extracted metadata, not
restored guest objects or complete executable/frontend acceptance.

An additional probe converted the authentic nine-node `ppExt` companion using
reflective research construction. It registered eight headers, prepared the two
original initializer fdecl bodies and supplied the exact `lean_st_ref_get` host
ABI. The unchanged initializer returned its current saved PPFns record while
all five callback body slots remained unprepared. Forking at the ref-read host
pause preserved aliases and isolated a host-side child-ref update. This does not
implement a public graph/global importer or execute Lean Ref.set. One observed
conversion/preparation/execution/fork probe took 6.3 ms caller CPU / 2.50 MB
cumulative allocation; it excludes original checkpoint extraction/authentication.

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

The implemented API uses a distinct `CodeRequest`, separate from `HostRequest`
and guest extern results.
The explicit driver suspends before entering an unprepared body, with a committed
activation containing target identity, accepted source identity, arguments,
return destination/kind, continuation and any AP surplus. No callee instruction
or initializer has run. `advance` at a code request returns without polling.
The recursive driver may explicitly reject unprepared execution; it must not
invoke a hidden loader or fall back to another interpreter.

`pendingCodeRequest()` returns only the active code request. Its defensive
accessors expose the issued Header/source/Name/digest/ABI and borrowed argument
views. `resumeCode(request, descendant)` preallocates and validates before
claiming, then enters the saved activation once. `failCode(request, cause)` marks
that branch terminal. `failureCodeRequest()`, `codeFailure()` and bounded
`codeFailureMessage()` retain diagnostics after failure. Convenience `invoke`
reports suspension; it never polls the loader. No request invokes a callback.

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

The implemented gates cover root/scalar/nested demands, nullary caching,
oversaturation across two code requests, shared captured owners and fork aliases,
host-reply overapplication, wrong/stale replies, independently linked sibling
callee IDs and injected failure after claim. The actual ppExt experiment now
forks at its first code pause; each branch demands the two original initializer
bodies independently, preserves the current saved PPFns record and leaves all
five callback bodies unprepared. That code-request probe used reflective research
graph construction, and ref mutation remains a host-side probe. The subsequent
[prepared-graph API](JAVA_PREPARED_GRAPHS.md) replaces Node construction with a
transactional importer for the genuine nine-node persistent slice and its two
ready globals; it does not yet cover the positive-RC nodes in the larger companion.

The [code-request implementation record](../measurements/java-ir-code-requests-2026-10-29.edn)
passes 10 focused code tests / 59 assertions and the combined isolated jar gate
of 359 executions / 13,493 assertions with a 384 MiB heap. Header-only recursive
rejection tests remain covered; explicit missing-code cases now exercise requests.
Paired warmed RBMap allocation remained 1,515,859.52 bytes per run. CPU medians
were recursive prior 2.314 ms / requests 2.247 ms and explicit 2.919 / 2.818 ms;
these shared-machine controls establish no speedup or native-performance claim.

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

First-release code/state distribution is described in
[the pinned frontend bundle plan](JAVA_FRONTEND_BUNDLE.md). A bundle avoids a
native build for runtime users; it does not supply missing Java runtime behavior.

Explicit source-backed extern-to-fdecl dispatch is documented in
[JAVA_GUEST_EXPORT_BINDINGS.md](JAVA_GUEST_EXPORT_BINDINGS.md). The actual target
Header remains the demand-code identity; original IR rows are unchanged.
