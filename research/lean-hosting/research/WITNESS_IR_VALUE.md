# Typed interpreter-declaration witnesses

This stage-2 transport passed independent native, host resolution and actual
hosted-helper checks and entered the full Init campaign. The later
[full Init result](../measurements/hosted-full-init-kernel.json) completed actual
guest finalization and strict checking of 65,994 constants. The subsequent
[hybrid check](../measurements/hosted-ordinary-hybrid-kernel.json) strictly rechecked
65,995 constants, and [source B](../measurements/hosted-ordinary-library-b.json)
passed its actual imported-source witness/calls after reviewed staged completion.
Those later bounded observations supersede the historical pending status; they
do not turn witness projection alone into frontend or package compatibility.
The stage-1 helper returns a guest Json value. The appended stage-2 helper,
`RuntimeCompileShim.exportEvalConstWitnessIR`, instead returns actual selected
Name and IR.Decl values. It introduces no declaration cache, initialization or
new execution authority. Existing interpreter selection, boxed resolution,
complete static dependencies, source origin and sorry evidence stay intact.
Host projection must reconstruct the exact earlier witness map before the
existing provenance, IR equality, ABI and executable-identity checks run.

The actual typed layout agreed with the host projector is:

- `EvalConstWitnessIRRow`: three object fields `name`, `decl`, `sourceModule`,
  followed by the sourceLocal Bool byte. The source declaration order places
  sourceLocal before sourceModule, but Lean moves object fields first.
- `EvalConstWitnessIR`: ten object fields `schema`, `producer`, `leanCommit`,
  `wordBits : Nat`, `target`, `name`, `boxedTarget`, `rows`,
  `missingDependencies`, `sorryDep`. Nat avoids another scalar-layout boundary.

Schema and producer strings deliberately match the earlier witness. The typed
helper itself is a separately trusted executable root; matching these strings
is not authorization. The caller owns its IO result; project the payload while
borrowing it, then release the result normally. The schema includes the exact
pinned Lean build and runtime profile as before.

## Native constructor oracle

`lean/IRValueWitnessOracle.lean` constructs 54 synthetic declarations that cover
all 13 Expr variants, all 13 FnBody variants and 14 IRType variants, with both
struct Option cases, both Alt/Arg/Lit variants, all four ExternEntry variants,
empty and mixed extern lists, all inc/dec Bool combinations, and both reuse
header flags. It includes Name strings with dots/empty segments, an arbitrary
numeric Name component above UInt64, and MPZ literal/variable values. These are
projection fixtures, not valid executable programs for every runtime profile;
union/struct projection does not claim runtime execution support.

A separate four-root fixture contains actual local, missing, imported and mixed
witnesses from real source compilation and owned module finalization. Their
explicit native typed-to-Json projection compressed to exactly the original
string witness in every case. No original check was omitted to achieve parity.

The deep fixture has two roots: an actual IR declaration with 4,096 nested
variable declarations, and its original native ToJson value. The expected Json
stays an object DAG instead of deeply nested manifest text. The host can compare
its stack-safe IR projection with its stack-safe guest Json projection without
relying on a recursive text parser or recursive Clojure equality.

All three object DAGs were compacted before export, so scalar storage extents
and padding are attested. The existing strict generic native producer rejects
unknown heap extents and unsupported execution objects. Native roundtrip checks
passed for the 168-node constructor fixture, 64-node typed-witness fixture and
61,499-node deep fixture. The shared exporter adapter is
`native/IRValueTransport.cpp`; it captures no program/world references.

Reproduction uses `scripts/build-witness-ir-oracle.sh`, after preparing the
owned source-module helpers and pinned exporter. Outputs live under
`target/witness-ir-value/`. Run serially when memory permits: the measured native
oracle process peaked at 829 MB RSS, higher than the initial small-process
estimate. The monitored run kept system available memory above 1.49 GiB and
never crossed the 1 GiB stop floor. These are resource observations, not speed
benchmarks. No live runtime binding was changed by this source/oracle work.


The finalized producer artifact is
`target/runtime-compile-shim-ir-value-source.jsonl` (473 rows), SHA256
`731bb72ce9928e0d46d50728c675df21a3d073c6d0f3c1dde96816af89c09cad`.
All 464 stage-1 rows are identical, the manifest is identical, and nine
new declarations add no initialization actions. Three additions are lazy closed
constants; link their ordinary closure without rerunning any old initialization.
The entry ABI consumes Environment (`object`), Name (`tobject`) and erased world
(`void`), returning owned IO (`object`), as the older helpers do. Retain borrowed
input owners before transfer.

The host projector's focused suite passed eight tests and 36 assertions at a
256 MB JVM limit, including all 54 native declarations, four actual witnesses,
the native 4,096-deep graph and a 5,000-deep model graph. These establish
projection parity and ownership, not live frontend adoption. The small tracked
record is `measurements/hosted-witness-ir-value.json`; the native artifact
comparison is `target/runtime-compile-shim-ir-value.diff.json`.

## Hosted adoption

The actual hosted helper returned the exact saved Json witness for the freshly
compiled `answer` declaration: two declarations, 1,594 guest steps, 403.7 ms in
the helper and 3.54 ms in host projection. This single diagnostic call includes
cold work and is not a comparative benchmark. The record is
[hosted-ir-witness-canary.json](../measurements/hosted-ir-witness-canary.json).

The transport and projector focused suite passed 15 tests and 329 assertions.
It covers native fixture resolution on all three backends, exact executable
identity, malformed payloads, profile/provenance rejection and owned IO errors.
The same witness validator remains mandatory.

The running full Init import was stopped before an unexecuted outer callback at
237,596,253 guest steps, with zero nested host boundaries. Additive preparation
checks both artifact digests, proves every predecessor row and manifest unchanged,
and admits only the nine new declarations. Existing function identities remain
unchanged. Resumption starts that pending callback once with typed transport;
completed initializer effects are not replayed. This checkpoint is in memory,
not a durable full-import archive.

## Dependency-walker experiment and actual profile

An appended linear dependency walker preserved all native and hosted witness
results, but did not improve the real paused `Lean.Parser.Tactic.simpa` witness.
Both variants selected the same 197 declarations. The original typed helper
used 3,285,202 guest steps and 21.826 seconds; the linear helper used 3,316,147
steps and 21.705 seconds. This diagnostic comparison shared a code cache and
used temporary heap-retention settings; it is not a competitive benchmark.
The linear helper has not replaced the running import's helper. See
[the paired record](../measurements/hosted-linear-witness-canary.json).

A temporary, automatically restored region profiler reproduced exactly
3,285,202 guest steps. About 45.4% belonged directly to the array map in
`Lean.EnvironmentHeader.moduleNames`; its associated array accesses and loop
arithmetic account for most of another 38%. Only about 0.3% belonged to the
dependency walker. Region attribution includes inlined work in its starting
owner and labels shared or unknown owners explicitly. See
[the profile](../measurements/hosted-witness-region-profile.json).

The helper computes `env.header.moduleNames` inside every imported row. For
197 rows over a 631-module environment this repeatedly materializes the same
array. An appended helper is being validated that computes the array once
within the invocation. It retains actual lookup, module provenance, complete
dependencies and the original dependency walker. It introduces no cross-world
cache. Native and hosted parity and same-input measurement are required before
adoption.

The shared-names helper subsequently passed four actual native witness parity
cases. Its artifact adds six declarations, preserves all 492 previous rows and
the manifest, and has no initializer actions. Its reachable closure excludes
the unadopted linear helper. The emitted outer helper computes module names
once; the loop uses the resulting array.

The actual same-input `simpa` canary preserved all 197 rows and reduced guest
steps from 3,285,202 to 560,411 (about 83%). Diagnostic helper time was 26.95
seconds versus 5.06 seconds; both used the same temporary retention settings and
shared code cache. These are not competitive benchmark results. See
[the shared-names record](../measurements/hosted-shared-names-witness-canary.json).
The full import has resumed with this helper from the exact pending callback.
Unused heap retention is temporarily reduced during the run and restored on
completion or failure; the 8 GiB maximum and external resource guards remain
unchanged.


## Remaining callback cost

A bounded observer sampled three normal callbacks after the shared-names change,
then restored all instrumented functions. It retained scalar timing/count data,
not guest worlds. For `Grind.showTerm`, `Grind.showGoals`, and
`Grind.grind_ref.quot`, complete handler times were approximately 2.99, 1.70,
and 1.47 seconds. Witness invocation accounted for 1.84, 0.76, and 0.62 seconds;
closure and authorization checks each took only tens of milliseconds. Only
119–131 guest steps occurred outside the witness invocation. These inclusive
measurements do not establish the cause of the remaining wall time; explicit
heap-transition measurements are the next diagnostic. See
[the callback phase record](../measurements/hosted-eval-const-phases.json).
