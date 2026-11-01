# Acceptance and memory followups, 2026-10-23

Static audit supplement to the [campaign continuation](CAMPAIGN_CONTINUATION_2026-10-23.md).
These findings do not establish genuine P2 acceptance, a runtime improvement or
reduced full-Init memory requirements. No tests, builds, JVM/native experiments
or changes to existing pinned sources were performed for this audit. P1 v2 subsequently stopped at the system available-memory guard during fresh
strict checking after 957.56 seconds. Its process was disposed and all 920 input
hashes matched; it produced no P1 acceptance result. Choose new P2 budgets only
after a future genuine P1 pass, not from this interrupted run.

## P2 corrections before a fresh coupled capture

The definitions-only P2 prototype remains under
`target/artifact-contract/project-current-consumer-v1/p2-prototype-v1/` from the
worktree root. Preserve it and prepare any executable revision separately.

1. **Increase the explicitly captured aggregate export bound to at least four.**
   The template currently has `execution.limits.max-exports = 2`, while P2 asks
   for A.nat, A.text, D.nat and D.text. The
   [`exports!` validator](../src/prototype/project_loader.clj) accumulates root
   counts across modules, so the second record would fail before discovery.
   The two-root and four-module limits do not change this independent bound.
2. **Provide bounded native-reset failure diagnostics.** The existing P1 graph
   extractor recognizes `:source-graph-import-state`, while
   [`native-failed!`](../src/prototype/resident_init_prefix.clj) records
   `:native-init-base-state`. Reusing the graph extractor would omit native
   used/reserved fuel. A new native extractor should preserve the original
   Throwable first, select only closed scalar fields, prefer the newest present
   state even if malformed, and retain bounded stdout fallback if reporting
   fails. Never serialize Worlds, Envs, Ref owners or full exception data.

The ordered independent roots [A,D] correctly target reset at the second leaf;
loading D alone or making D depend on A does not. The prototype observes native
readiness0 through N and completion at module index1, before the final graph
import at index2. Public success and the native finalizer's checks are still
required; descriptive progress is not readiness authority or independent final
guard/extension parity.

Both source fixtures currently implement identity. A separately captured D with
distinct Nat/text results would improve detection of accidental A/D dispatch
substitution. If selected, update the hardcoded D hash, payload bytes and call
expectations together; this is a strengthening of the fixture, not evidence of
an existing dispatch defect.

After P1 passes, bind its actual plan/result/guard receipt/disposed all-input
postcheck. Refresh the coupled template's old P1 controller, embedded sources,
controller provenance and both controller inventories consistently. Derive the
expected native-query count/order from the exact Init-plan closure and unique
valid all-phase witnesses using
[`native-init-metadata!`](../src/prototype/globals_consumer_factory.clj), and pin
every derivation input. Do not infer that count from initialized guard totals.

Keep P1's version alive through all P2 calls and cleanup, close each returned
call version independently, then call retained P1 before its original owner
finishes. Review the fresh coupled runner/guard/payload and native failure
diagnostic. Native reset and the two-root final import have costs not established
by successful P1 or the constructed-prefix G1 benchmark; choose no automatic
fuel escalation or presumed resource envelope here.

## Three memory and turnover candidates

### 1. Reuse compact dependency planning in the first-pass Init checker

**Source finding:** [`imported-kernel/checking-plan`](../src/prototype/imported_kernel.clj)
isolates construction-only groups/name/dependency structures in one frame and
uses transient reverse-edge construction. The actual strict first-pass
[`compact-import-check/verify-constants`](../src/prototype/compact_import_check.clj)
still duplicates the older inline construction and refers to the full group
vector during admission. Both implementations exist in the selected capture.

**Existing evidence:** the
[plan lifetime record](../measurements/kernel-check-plan-lifetime.json) has
15 tests / 168 assertions, including exact schedule/error and deterministic
non-retention checks. The
[reverse-edge allocation record](../measurements/kernel-check-graph-allocation.json)
reports median allocated bytes of 84,302,272 for the historical builder and
12,189,984 for the candidate on a synthetic 16,384-group/131,036-edge graph.
Some small cases allocate more or run slower. This does not measure Init peak
RSS, retained graph bytes, strict-check latency or full-frontend speed.

**Tiny probe:** extract/reuse the pure plan while retaining compact projection,
exact policies and all Java admission calls. Compare old/new schedules, missing
dependency and cycle errors, exact CI identities and checked environments on
empty/singleton/chain/diamond/fan cases plus the existing native17-CI fixture.
Reuse deterministic non-retention controls, stopping at intentional member/key
roots. Measure paired allocations on one modest graph in a separately guarded
small JVM; do not restore full Init for this local question.

### 2. Validate wire rows without discarded transformed copies

**Source finding:** [`checkpoint-wire/wire-value`](../src/prototype/checkpoint_wire.clj)
reconstructs container trees and transforms floating scalars for wire comparison.
`decode` calls it for validation but returns the original parsed row.
[`restore-consumer/world!`](../src/prototype/restore_consumer.clj) invokes it again
on executable/heap/global/state rows and discards the transformed results before
its separate live-reference walk. This is temporary allocation visible in
source, not a measured dominant restore cost.

**Tiny probe:** add a non-transforming validator only at call sites ignoring the
returned transformed tree. Keep the existing transformer for encoding and
raw-float comparisons, and initially retain the separate reference-validation
walk. Compare acceptance/rejection against the old validator on small rows with
metadata, guest carriers, malformed records/custom maps/sets, raw Float/Double
bits, NaN/signed zero and floats nested inside map keys or set members. Require
unchanged original decoded row identity and exact metadata/value behavior.
Measure allocations on bounded repeated rows. Preserve digest/count/trailer/EOF,
resource acquisition and executable-authority checks unchanged.

### 3. Hand off successful preparation ownership without obsolete escrow roots

**Source finding:** campaign restore/check/helper/admission controllers retain
intermediate packets for provenance and diagnostics. The public
[`Project loader`](../src/prototype/project_loader.clj) already compacts some
completed controls; generic compaction is not a new missing feature. Remaining
controller snapshots may retain extra state, but their incremental bytes are
unknown because persistent packets share data.

**Tiny probe:** design a future success-only handoff retaining issued Projects,
the borrowed pristine baseline, exact certificates/bindings, Source lease and
deliberate old versions. Drop intermediate controller roots only after their
consumers no longer require them. Use small real ownership chains, compare
public calls and retained-fork behavior, and use deterministic root walks with
negative controls to identify obsolete packet retention. Inject failures on
either side of the handoff: failed packets and original ownership evidence must
remain intact. Never prune caller-owned REPL snapshots or implicitly close a
shared Source. Only later measure repeated load/edit/close with a fixed retained
version count; process disposal alone is not service cleanup.

## Existing work and execution discipline

Restore already uses streaming authenticated frames, transient tables and exact
Name-prefix sharing, clearing its interning map after parsing. The compact
projector memo already belongs only to bulk projection and drops before graph
construction. The current consumer already includes globals first-mutation
storage and bounded weak register-width caching. Historical JFR findings that
motivated those changes must not be presented as evidence they are unimplemented.
See [execution performance](EXECUTION_PERFORMANCE.md),
[globals boundaries](GLOBALS_BOUNDARY_OPTIMIZATION.md) and
[register sizing](PROGRAM_SLOT_CACHE.md).

Candidate1 is the strongest immediate local experiment; candidate2 is independent
restore validation work; candidate3 belongs to warm-session lifecycle design.
No full-run benefit has been measured for these proposals. Preserve fresh strict
checking wherever the acceptance contract requires it; reuse of immutable
projection facts is not reuse of checking verdicts. New runtime code requires
a reviewed consumer identity/compatibility decision and fresh selected capture.
Keep historical P1 inputs untouched and use one guarded semantic process at a time.

## Subsequent focused implementation

The isolated compact first-pass checker now delegates to the existing compact
plan. [Focused validation](../measurements/compact-first-pass-plan.json) passes
22 tests / 235 assertions, including the actual native17-CI certificate/ownership
checks, historical scheduling/non-retention controls, and missing/cyclic
dependency errors through the compact verifier. Its 384 MiB heap run peaks at
447,676,416 bytes process-group RSS and completes in 9.97 seconds. All 584 input
hashes match after disposal. This is focused correctness evidence, not a measured
full-Init memory or latency improvement. The first test attempt's incorrect
self-reference fixture and correction are retained in the validation record.

The [full-run resource observation](../measurements/project-p1-memory-stop-oct23.json)
records the earlier interrupted P1 v2 separately. No new full consumer capture or
public P1 acceptance follows from the focused pass.
