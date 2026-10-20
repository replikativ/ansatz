# First hosted command elaboration gates

Pinned producer/runtime source: Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. This research chronology separates
completed hosted milestones from native oracles and remaining experiment gates.

## Fresh source-module continuation (2026-10-20)

The [source-module progress receipt](../measurements/full-init-source-module-progress.json)
records a separate pre-user branch of the checked full Init environment. An
explicit source-import profile independently derives 258 helper functions,
including two export wrappers absent from the lazy original closure. Existing
executables remain identical. The earlier preparation assumption that those
wrappers were already linked failed before guest execution; its controller is
retained separately. Helper manifests have legacy provenance limitations recorded
in the receipt; this is a new reviewed host profile, not original-factory authority.

The actual helper value initializer executes once in five guest instructions.
`OrdinaryLibraryA.lean` then compiles, initializes and returns Nat42 in 34.310
seconds with no diagnostics or local initializer actions. The complete genuine
compilation packet authorizes publication; a FileHandle alone is insufficient.
Lean's guest helpers assemble A with the 631-module native Init prefix and B's
actual parsed `[Init, meta Init, OrdinaryLibraryA]` header in 16.662 seconds.
Genuine Init+A finalization, fresh strict union checking and B execution are
subsequent gates, not established by assembly. These scoped timings include
hosted execution and are not competitive benchmarks.

The monolithic finalizer call subsequently exhausts its enclosing 100M guest
instruction budget inside a child helper. That does not establish an intrinsic
100M helper cost. The paused child has no resumable host continuation; the failed
branch is terminal and is not replayed. The original resident profile still
passes immediately before whole-process disposal, after all source workers join.
Process exit zero records disposal, not source-finalization or semantic-cleanup
success. A fresh attempt should use the existing cooperative driver with separate
2M outer slices, 20M helper-completion budgets and an explicit 500M total cap.
That fresh guarded pipeline is now launched after independent source/ownership,
launcher and frozen-pin review, definitions compilation and generated-code reader
checks. It restores the saved Init IO and repeats strict checking before the new
source experiment. That attempt now completes genuine Init+A finalization in
300,115,127 guest instructions (993.347 seconds), then freshly checks all 65,995
declarations and records the exact A-only receipt (121.792 seconds). B subsequently
fails source-import authorization with `Source import witness differs from admitted
source unit`; no successful B compilation/call or origin-witness result follows.
The guarded process exits one after recording the terminal failure. These timings
are scoped observations, not competitive benchmarks. The next gate is a targeted
module/IR/runtime witness comparison, without weakening admission checks.

Consolidation should separate independently authorized code preparation from
guest value readiness, preserve optional genuine publication receipts through
the resident facade, and expose assembly/finalization/checking as distinct
one-shot operations. Tests should cover absent/already-linked helpers,
candidate-only collisions, initializer ownership/failure, stale or wrong-world
receipts, source/header drift and prevention of replay. Keep the current
initializer-free classic-over-Init profile explicit.

## Full Init strict and resident acceptance (2026-10-20)

The [new full-profile sequence](../measurements/full-init-strict-resident-acceptance.json)
freshly checks all 65,994 actual guest declarations with the compact consumer and
associates the exact guest root/map/quotient state. Its receipt records 15 admitted
axioms/assumptions, including `sorryAx` and compiler/runtime assumptions. The
original 242-input runtime/factory remains unchanged; consumer identities are
separate. Independent repeated native whole-map/extension-state parity is still open.

The same checked environment passes resident adoption and ordinary implicit-Init
source execution: Nat42, macro expansion returning Nat42 and unchanged Unicode,
an invalid file producing two diagnostics without a handle on a successfully
closed fork, and exactly two explicit Lean-to-Clojure callbacks returning Nat42
and Unicode. There is no native per-input compiler. The diagnostic phase took
1.782 seconds; the interop phase, including binding/compilation/initialization and
two calls, took 36.668 seconds. These are scoped monotonic observations, not a
competitive performance benchmark. Source-module A-to-B publication/import/edit,
public packaging and broad package/FFI coverage remain separate gates.

A separate small verified Store also confirms that the genuine compact-consumer
certificate can supply projection reuse to the original verifier while every CI
is checked again from a fresh Java Env. The fixture Source closes after the check;
this is compatibility evidence, not independent full native parity.

## Full Init finalization and durable capture (2026-10-20)

The [fresh Oct20 run](../measurements/full-init-finalized-capture-oct20.json)
completed the actual guest finalizer and captured its successful IO result before
strict checking. The checkpoint contains 334,467 functions, 776,060 heap objects,
56,125 globals and 13,003 imported declarations; its data stream is 610,021,608
bytes. The externally retained manifest digest was verified independently. No
`evalConst` failures were recorded. The producer subsequently reached its 5,400-second
REPL lifecycle limit after publication; that process stop is separate from capture
success. A fresh JVM subsequently restored the exact captured counts and native
source without replay. The original strict projection attempt then spent prolonged
time in full GC near its unchanged 3 GiB heap limit and was explicitly resource-stopped;
this establishes neither kernel acceptance nor semantic rejection. A separately
pinned compact checking consumer preserves the original runtime/checkpoint identity
and strict rules while reducing projection-memo overhead. Its small-fixture validation
preceded the genuine full strict and ordinary implicit-Init resident acceptance above.
Native-map/extension-state parity and source-module import/edit remain separate gates.

The isolated parent library suite also passed after reboot: 822 tests and 3,591
assertions, with no failures or errors. Optional Mathlib integration was excluded;
earlier resource/shared-store attempts remain historical evidence below.

## Fresh full Init resource stop (2026-10-18)

The [fresh full-Init v4 run](../measurements/full-init-fresh-resource-stop-v4.json)
was terminated by the unchanged global available-memory guard before guest
finalization completed. It observed 82,266,885 finalizer steps beyond the
25,048,592-step bootstrap/assembly base and 320 `lean_eval_const` boundaries.
The last complete campaign summary reported zero callback failures; the last
observed callback boundary has no completion receipt. Peak process-group RSS
was 3,384,029,184 bytes, below its 3,584 MiB limit, but system-wide available
memory fell below 1 GiB. The 745.99-second lifecycle is an interrupted run,
not full startup or finalization latency.

The approved full-profile factory constructor and the reviewed capture control
loaded successfully. The queued capture required actual finalizer success,
so no checkpoint was published, no fresh full strict checking occurred, and
there is no resumable active guest state. Full-profile restoration and ordinary
implicit-Init source acceptance were open gates at that stage; the Oct20 results
above supersede that status. This resource stop does not
invalidate the separately recorded fresh standalone KernelImportProbe results
or establish a guest semantic failure. Another heavy run requires adequate
stable system headroom under the existing launch and execution limits.

## Post-restore strict-checking readiness (2026-10-18)

The definitions-only [restored import checker](../scripts/RESTORED_IMPORT_CHECK.md)
adds a separately testable consumer for a completed/restored guest IO result. It
validates independent helpers and host bindings, calls the existing whole-map
checker once, and preserves exact owners and newer callback sessions on failure.
It does not restore an archive, replay finalization or own the native source lease.
The tests execute model helper IR with genuine native ConstantInfos and actual
strict Java checking; they are not a fresh full-Init acceptance result. Existing
source-bound factory inputs and the ignored v4 control files remain unchanged.
[Validation](../measurements/restored-import-check-validation.json) records 9 focused
tests / 107 assertions and 791 runtime tests / 66,396 assertions, all passing.
The new final sources pass focused revalidation after whitespace-only formatting.
The parent source suite could not complete against read-only shared Mathlib; the
isolated known-profile launch then refused insufficient memory headroom. No fresh
parent-suite, full Init or checkpoint-restore success is inferred.

## Resident facade preparation (2026-10-18)

The explicit facade passes its actual archived-prelude REPL and fresh-JVM sequences: identity
over Nat and Unicode String, a second source, an expected diagnostic, and two
Lean-to-Clojure callbacks. See the
[source/class-pinned observation](../measurements/resident-preparation-progress.json)
and [facade scope](RESIDENT_FRONTEND_API.md). Name-prefix sharing restores the
entire authenticated archive with about 1.12 GB (1.04 GiB) retained after host GC, where
the unshared 3 GiB attempt saturated its heap. Existing executable bodies now
receive dependency completion before trusted identity capture. No initializers
or source statements are elided by these storage/linking changes.

The successful REPL segment took 47.2 seconds from an already restored archive.
The later fresh-JVM run, against the safety-validated rebuilt kernel, took
163.58 seconds including startup and authenticated archive restoration. Neither
uses a native per-input compiler. These are prelude-only facade observations,
not a replacement for
the earlier ordinary-Init chronology below or proof of general package coverage.

## Proposed coordinated Lean 4.33 bundle completion

The remaining sequence is proposed work, not a shipped capability. The shipped bundle
remains the explicitly inventoried legacy cohort. The current staging generator
has checked the three candidate kernel closures and their overlaps, but metadata
target closure remains incomplete; no generated replacement has been promoted.
The effective-unsafe-definition checker fix passed its focused regression,
including rejection of a safe theorem through an unsafe wrapper. That fix does
not retrospectively certify previously loaded environments.

1. **Strict non-safe admission foundation is implemented.** The
   [vector and streaming replay paths](../../../src/ansatz/export/replay.clj)
   now share finite batch admission with the lazy prelude loader. Streaming
   retains its checked prefix and buffers the suffix from its first non-safe
   definition, potentially most of a large input. Pinned Lean `Declaration.lean`
   defines `DefinitionVal.all` as user mutual-block bookkeeping, not kernel
   admission-group authority. That field is preserved; actual body-reference
   strongly connected components determine recursive groups. The checker
   validates headers before extending the environment and enforces equal safety
   and ordered universe parameters. Missing dependencies and incomplete packages
   fail. Tests cover self/mutual recursion, interleaving, misleading `.all`, mixed
   safety, header cycles, and safe references to non-safe declarations, alongside
   a captured native kernel
   [comparison](../../../test/ansatz/export/fixtures/non-safe-native-4.33.md).

2. **Introduce a versioned checked-runtime-CI generation profile.** Retain the
   existing six resource roles and legacy profile. The proposed profile records
   unsafe export explicitly and strictly checks every emitted declaration; it
   does not replace bodies with axioms or skip checking. Record exact unsafe,
   partial and axiom inventories, the accepted axiom policy, producer identity,
   and all derived-root evidence. Limit export to selected roots and their
   dependency closure. Admitting declaration data grants no automatic extern
   capabilities, `implemented_by` execution, or authority to convert runtime
   results into proofs. A separate runtime artifact lane is unnecessary for this
   bounded release and would add another loading/identity boundary.

3. **Compute metadata closure separately for each kernel role.** The current
   [candidate validator](../../../scripts/validate-bundle.clj) selects companions
   against the union of `init`, `lex` and `sizeof`; this can hide a target absent
   from the initially active Env. The pure metadata planner now exposes per-role
   missing roots and typed edges, including an explicit planner-only witness
   profile; generator wiring and serialized profile support remain open.
   For each role, repeatedly export its closure,
   select applicable metadata, and add referenced targets, witnesses, instance
   classes and unfolding theorems until no roots change. Record each edge and
   iteration; unresolved names or an exceeded iteration bound fail. Explicit
   public roots and derived private compiler dependencies remain distinct policy
   categories. Keep actual native names and metadata instead of silently dropping
   unsupported rows. Generated metadata must also preserve structured Name
   identity, or reject names that cannot round-trip through the consumer's
   representation. [Java Name](../../../src-java/ansatz/kernel/Name.java) parses
   dot-separated numeric components rather than Lean's quoted-identifier grammar;
   string components containing dots or numeric text can otherwise disappear or
   collide during selection. This is a proposed profile gate, not an observed
   failure in the current Init cohort; structural expression equality is unaffected.

4. **Preserve typed csimp witnesses.** The
   [attribute dumper](../../../scripts/dump_attrs.lean) currently loses the
   `thmName` carried by native `Lean.Compiler.CSimp.Entry`. A versioned metadata
   row must retain it, include it in closure expansion, and validate its checked
   equality type against the source/target constants and native universe-argument
   constraints. Require a safe proof-bearing witness under the explicit axiom
   policy, not merely an existing name. Preserve this evidence through Env
   installation. `implemented_by` instead records a type-compatible runtime
   implementation, not an equality proof; it must never become a proof rewrite.

5. **Complete active Env companions and release acceptance.** The
   [lazy prelude loader](../../../src/ansatz/wf.clj) currently adds declarations
   without refreshing attrs, matchers or instances filtered during initial
   setup. Prepare checked declarations and newly applicable companion extensions
   together, preserve user extensions, invalidate affected caches, and activate
   through the existing session boundary. Reject conflicting declarations;
   matching names or a sentinel alone are insufficient. Test both prelude orders,
   idempotence, new instance/simp visibility, session isolation and failure
   atomicity. Promotion additionally requires strict independent replay, exact
   overlaps, witness validation, bundled activation and representative compiled
   calls. Unsupported selected simp semantics remain an activation failure;
   [codegen](../../../src/ansatz/codegen.clj) must retain its actual lowerability
   checks. Checked metadata presence is not general native runtime support.

## Hybrid finalizer completion and strict kernel admission

The [actual Init-plus-OrdinaryLibraryA finalizer](../measurements/hosted-ordinary-hybrid-finalization.json)
completed at guest step 920,855,277 without replay or native per-input compilation.
It took 320,635,990 guest steps in total; 138,465,856 steps and 463,774.471405 ms belong
to the resumed segment from checkpoint 782,389,421. That timing is not complete
fresh-import latency. The completion record intentionally precedes strict host
checking.

The separate [strict whole-map admission](../measurements/hosted-ordinary-hybrid-kernel.json)
passed 65,995 constants with 15 explicit axiom assumptions in 122,020.048528 ms.
All constants were rechecked from a fresh Java Env. Only authenticated immutable
Java projections were reused for unchanged native CI references under exact
Store identity/no-shadow guards; no prior checking verdict was substituted.
All native CI references were preserved, and A's receipt covers its one source
constant under the actual protected whole-map anchor.

OrdinaryLibraryB's guest compilation completed at cumulative step 947,201,719,
but final output installation failed closed for `ordinaryLibraryIdentity._redArg`:
`Source import lacks checked module installation authority`. The returned
header-only kernel root lacked an association, while prior checked roots preserved
the source JavaCI identity. That failed gate remains part of the chronology.

After the reviewed strict same-map/quotient header-association fix, the
[actual B completion](../measurements/hosted-ordinary-library-b.json) passed the
real `_redArg` imported-source witness path and returned 42 plus
`"Imported source: λ 🦉"`. It records no diagnostics, `ready`, zero pending
initializers and one release per returned owner. Its 1445.772123 ms covers only
completion/installation/initialization/calls; the earlier guest compilation and
finalizer were not replayed, and no native per-input compiler was used. This is
the bounded ordinary Init-plus-A imported-by-B success, not arbitrary module or
package compatibility. See
[HOSTED_SOURCE_MODULES.md](HOSTED_SOURCE_MODULES.md#completed-guest-finalization-and-whole-map-checking).

The [final experiment regression](../measurements/hosted-source-header-regression.json)
after the header-association fix passed **691 tests / 58,784 assertions**, zero
failures/errors, in 159.944 seconds under the 256 MiB guard. All 192 recorded
source/test hashes remained unchanged. This validates that experiment generation;
it does not stand in for the separate parent Ansatz source/AOT/JAR checks.

## Same-checkpoint restoration adoption during hybrid finalization

At guest step 782,389,421, the paused pre-handler state passed
[register-restoration adoption](../measurements/hosted-register-restoration-adoption.json):
120,330 total slots became 2621 despite global width 4011, with exact frozen state,
Machine class, sentinel, heap and functions preserved. The
[storage-hint adoption](../measurements/hosted-heap-storage-hint-adoption.json)
validated 1,386,420 local nodes cold and zero warm, including proof preservation
through actual host retain/allocate/replace/release operations. Hints are only
storage-shape evidence for existing COW, never deep immutability or kernel trust.
The same guest checkpoint resumed at 15:59:47 UTC on 2026-10-17 without finalizer
replay. Globals/frame/local restoration remains real work; there is no O(1)
entire-fork or paired speed benchmark claim.

[Source-pinned combined regression](../measurements/heap-storage-regression.json)
passed 688 tests / 58,628 assertions. The
[earlier allocation diagnostic](../measurements/hosted-hybrid-finalizer-allocation-profile.json)
identified heap traversal and bindings costs; it is not a performance comparison.
At this adoption point the genuine hybrid guest finalizer was still running;
the later completion/checking above is recorded separately. B later passed the reviewed installation/call gate
as described above. See
[REGISTER_LAYOUTS.md](REGISTER_LAYOUTS.md#restoring-live-continuations-and-warm-heap-storage)
for the precise warm/cold boundary.

## Current ordinary interop evidence

Fresh hosted [OrdinaryInterop.lean](../fixtures/hosted/OrdinaryInterop.lean)
compilation and Nat/Unicode String callbacks passed with no diagnostics or pending
initializers ([measurement](../measurements/hosted-ordinary-interop.json)).
A separate [already-compiled heap probe](../measurements/hosted-ordinary-interop-heap-forks.json)
then used `hosted-file/finish-file` for two independent forks of an owned heap
String Ref. Both returned the same Ref/id at RC1, exactly two host callbacks ran,
and releasing each returned owner once preserved the other fork and seed. This
probe took 1072.785908 ms for execution/checks only and did not compile source or
invoke a native per-input compiler. It proves this heap-ownership/fork case under
the text-backed String profile, not arbitrary FFI or effect safety.

The earlier ordinary-gate regression was **663 tests / 58,127 assertions**;
the later source-pinned restoration/storage regression above is **688 / 58,628**. Native-produced
bootstrap/import artifacts and an explicitly prepared resident context remain
required. The [resident facade design](RESIDENT_FRONTEND_API.md) is a proposal;
ordinary source-module imports alongside Init still need the explicit hybrid
profile in [HOSTED_SOURCE_MODULES.md](HOSTED_SOURCE_MODULES.md).

## Full Init import and first ordinary-file success (2026-10-17)

The actual guest import finalizer completed for the default `Init` import. Its
final checked constant map then passed the Ansatz association gate: **65,994
constants and 15 declared axioms**. The
[measurement](../measurements/hosted-full-init-kernel.json) records explicit
`allow-axioms`, `allow-unsafe`, and `allow-compiler-markers` policies, with no
native finalizer substitution and no resident `TypeChecker` redefinition.
Axioms remain assumptions; these policies do not skip declaration checking or
canonical quotient checks. The resulting association belongs to the exact
owned guest kernel root and constant map, rather than an unrelated native
Environment pointer.

The record reports 571,074,382 cumulative guest finalization steps and 779,005
local heap objects. These are campaign observations, not a clean-start latency
or steady-state file throughput benchmark. Native-produced, verified bootstrap
and ModuleData artifacts remain inputs to the experiment.

[OrdinaryAnswer.lean](../fixtures/hosted/OrdinaryAnswer.lean),
`def ordinaryAnswer : Nat := 42`, now passes hosted compile/initialize/call
against the genuinely finalized, strictly associated environment, with its normal
implicit `Init` imports. The
[ordinary-answer measurement](../measurements/hosted-ordinary-answer.json)
records result `[42]`, no diagnostics, zero pending initializers, initialization
state `ready`, and **74,286.986266 ms** for this run. It used no native per-input
compilation. This establishes this concrete ordinary-file path; it is not a
steady-state throughput benchmark or evidence that arbitrary Lean files work.

The first attempt had stopped at unsupported `lean_expr_quick_lt`
(`Lean.Expr.quickLt`). Its saved failure reported last frozen checkpoint step
581,338,077, not the exact trapping instruction. After the primitive and exact
executable-row update, the successful run used an independent prepared fork;
it did not repeat the completed full-Init import. The earlier
[source-import result](../measurements/hosted-source-import.json) establishes the
smaller prelude A-to-B path separately.

The subsequently successful fixture is
[OrdinaryMacro.lean](../fixtures/hosted/OrdinaryMacro.lean), which defines
`hostedIdentity` syntax and a polymorphic `macroAnswer`. Its first hosted run
failed with `Runtime extern arity mismatch` for `lean_string_utf8_set`; see the
local [macro diagnostic log](../target/frontend-run-ordinary-macro.log).
That attempt used a runtime validator selecting fixed `:arity 4` before the
same symbol's permitted `:arities #{3 4}`, rejecting the supported three-argument
call before the string implementation ran. After correcting that validator, the
actual next attempt advanced to a strict evalConst reuse rejection at last frozen
checkpoint step 597,803,422. Its retained exported bundle contains 12 declarations;
`Lean.Name.str._override._closed_0` has exactly the same IR as its recorded
imported authority, but the exported row labels it `value` while the canonical
source capture labels it `closed` (both have no initializer). The
[retained-bundle diagnostic](../target/frontend-inspect-macro-retained-bundle.log)
was extracted from the failure snapshot without executing a guest helper or
replaying the handler.

Pinned `Lean/Compiler/ClosedTermCache.lean:22–38` stores closed-term membership
in a non-persistent `EnvExtension`;
`Lean/Compiler/LCNF/SimpleGroundExpr.lean:87–99,129–130` does the same for
simple-ground classification; `RuntimeCompileShim.lean:110–115` re-infers
runtime roles from the current environment. This makes imported classification
loss a concrete producer-context issue. It does not justify changing executable
IR, ignoring initializer differences, or changing a local source unit's runtime
metadata. Source-bundle reuse now preserves previously authorized imported
`closed` or `ground` classification only when the incoming zero-argument
declaration has exact IR,
`sourceLocal = false`, runtime `value` with no initializer, and an existing
imported authority recording `closed` or `ground` with no initializer. Interpreter
witness checks and local source-unit runtime checks remain strict; conversion
between `closed` and `ground` is rejected. This preserves the existing memoized
global and executable instead of reconstructing native static objects. The
original bundle bytes or unreconciled map rows still define its digest. Focused
regression coverage passes 21 tests / 438 assertions
across reference, mutable, and JVM backends, including code/global identity,
forks, changed IR, initializer, source-local, and runtime-bearing witness rejection.
A further actual attempt reached the analogous `ground`-to-`value` rejection.
Its retained bundle contained 82 rows / 157,497 characters and again had exact
IR. After the canonical imported classification fix, the reviewed paused run
completed successfully: [the macro measurement](../measurements/hosted-ordinary-macro.json)
records `[42]`, no diagnostics, zero pending initializers, and state `ready`.
This exercises source-defined `hostedIdentity` syntax and the polymorphic
`macroAnswer` through the actual hosted frontend with implicit Init, without a
native per-input compiler.

That successful continuation began at cumulative guest step **642,225,888**.
It explicitly retried only the reviewed pure `lean_eval_const` prefix after
releasing the retained exporter IO owner once; prior source elaboration was not
replayed. **100,724.634313 ms measures the resumed segment only**, including
result finishing and the requested call. It is not whole-file compilation time,
a fresh-run macro timing, or a throughput benchmark. See the
[reviewed recovery log](../target/frontend-resume-macro-reviewed.log). The
separate interop run below supplies its own evidence; it is not inferred from
macro or Nat42 success.

The separately executed [OrdinaryInterop.lean](../fixtures/hosted/OrdinaryInterop.lean)
also passed a fresh file run against the prepared ordinary environment. The
[interop measurement](../measurements/hosted-ordinary-interop.json) records two
actual Lean-to-host callback entries, returning `42` and
`"Lean ↔ Clojure: λ 🦉"`, with no diagnostics, zero pending initializers, and state
`ready`. The polymorphic Lean `@[extern "ansatz_host_identity"]` opaque and its
ordinary wrapper were compiled and installed by the guest frontend. The Clojure
handler validated each borrowed view and transferred the same owned payload
back; the caller decoded and released each returned owner once. No native
per-input compilation was used. See the
[actual interop log](../target/frontend-run-ordinary-interop.log).

Its **45,138.887217 ms** covers this prepared JVM file run, initialization, and two
calls with compile threshold 64; it excludes bootstrap preparation and is not a
steady-state or clean-machine benchmark. This proves the concrete owned identity
callback with Nat and Unicode String values, not arbitrary native ABI coverage.
Native Lean-produced bootstrap and verified import artifacts are still required.
Loading a newly compiled source module as an import alongside the full Init
dependency graph is not implemented; the smaller prelude A-to-B source-import
result remains separate. Individual files using the already finalized Init
environment are the path exercised here.

Independent fork reruns are scoped to the exact pure Nat42 definition and fixed
capabilities reviewed here. The prepared world/session/environment remain
borrowed; a failed branch remains available for inspection. This does not
authorize replaying an arbitrary initializer, macro, user handler, filesystem
write, or external call. Inspect actual binding signatures/handler identities
and effect records without invoking handlers. An empty `:events` vector is not
proof that external IO did not occur: it records modeled runtime events, not a
complete host-effect audit.

`raw/continue` failure metadata identifies the last frozen snapshot and matching
active session. A mutable/JVM trap can occur later within that execution chunk.
A nested helper checkpoint additionally lacks the suspended outer Clojure
callback continuation; using it as though it were the complete file result is
incorrect. Preserve `:host-boundaries`, parent/helper-entry snapshots, frontend
IO-result alternatives, and their matching sessions. Neither child resume nor
parent rollback is an automatic retry policy.

## Explicit finishing of completed compilation

`prototype.frontend/finish-compilation-refs` accepts an independently completed
raw `compileImportedFileState` result, the original `:file-name`, borrowed guest
`:roots`, and the same installation configuration as `compile-file-refs`.
The result must be `:done`, its value must equal the world's result, and its
session must carry the identical function map. It shares the normal IO cleanup,
envelope validation, owned Environment retention, and strict bundle installation
path. It does not resume execution or retry a host handler.

`prototype.hosted-file/finish-file` accepts that compiled result and the original
execution request. It shares the normal explicit `:defer`/`:run` initialization
and admitted-entrypoint calls, without reading source or recompiling. Completed
call results and newer error checkpoints remain owned and separately inspectable.
The ordinary APIs delegate to these finishers, preserving validation before a
guest compilation call.

A manually reviewed recovery must first produce a genuine completed raw result.
A failed host callback snapshot is insufficient. If the original structured-name
layer saved `:frontend-temporary-owners`, those owners remain the caller's
responsibility: keep its encoded roots alive through result finishing, then
release each original temporary once in the returned world. Failed branches are
immutable alternatives, not additional owners to release in another branch.
Neither finisher authorizes retrying a callback or replaying external effects.

The actual macro recovery above used this exact staged sequence: complete the
resumed guest `compileImportedFileState`, pass its actual raw result to
`finish-compilation-refs`, release the original structured layer's module/roots
temporary owners in the returned world, then pass the compiled result to
`finish-file` for explicit `:run` initialization and the admitted `macroAnswer`
call. Session/function identity, the live verified native source, the borrowed
handler ABI, the retained rc1 exporter wrapper, and the pre-install validation
failure were checked before continuation. The existing guest function map was
not replaced during runtime-function adoption.

Focused staged-finisher coverage is separately **23 tests / 342 assertions**
using explicitly modeled helper envelopes, captured IR, and genuine raw
pause/continue across all three backends. Those tests verify orchestration and
ownership; the linked actual macro record supplies the frontend recovery result.

## Expr metavariable integration evidence

The subsequent `runtime-expr-mvars` implementation was validated against 22
native differential cases, including direct-assignment writeback, delayed
assignments under binders, beta reduction, shared expression identity, and level
metavariables. Its focused suite also checks paused/forked execution across the
three compiled backends: two tests, 1,290 assertions passed. The full regression
reported 482 tests and 24,018 assertions with no failures or errors.

`lean/ExprMVarsProbe.lean` adds six integration calls using genuine guest MCtx
assignment maps and helper functions, rather than the differential test's
independent map adapter. Native and hosted execution agree:

| Seed | `directSummary` | `delayedSummary` | `cutSummary` |
| --- | ---: | ---: | ---: |
| 0 | 11 | 11 | 111 |
| 7 | 18 | 18 | 118 |

The direct case checks assignment-chain writeback; delayed checks substitution
and binder lifting; cut checks normalization of an unresolved delayed assignment
without incorrectly assigning its pending metavariable. Each result includes
the seed, so the second row also checks genuine argument flow.

Reproduction artifacts are `target/expr-mvars-probe-source.jsonl` (67 rows,
zero initialization actions, SHA256
`1a90985bec8c6ac67026ca93c16b0013fe4b13d8f397f1c292b510acc37412f3`),
`target/expr-mvars-probe-native.jsonl`, and
`target/run-expr-mvars-probe.clj`. The latter links against the existing resident
frontend catalogue/functions/world/bindings without reloading namespaces or
modifying that ready world. The parent executed it successfully in a separate
world with 119 additional functions; its log is
`target/expr-mvars-probe-hosted.log` (first call approximately 521 ms; remaining
calls approximately 98–125 ms).

These are hosted primitive integration checks. They do not establish complete
file elaboration, imports, or source-module publication.

## Runnable fixtures

`lean/HostedFrontendProbe.lean` imports `Lean.Elab.Frontend`. Its source-local
producer bundle is `target/hosted-frontend-probe-source.jsonl`. All public IO
entries have a final raw `void` world parameter. Use the unboxed entry name,
not its generated `_boxed` adapter:

```clojure
(interop/call-io session "HostedFrontendProbe.emptyEnvironmentSummary" []
                 {:arguments [] :result :nat})
(interop/call-io session "HostedFrontendProbe.processSummary"
                 ["axiom HostedSort : Sort 1\n"]
                 {:arguments [:string] :result :nat})
(interop/call-io session "HostedFrontendProbe.elaborateAndRunSeededIdentity" [42]
                 {:arguments [:nat] :result :nat})
```

Link these roots against the complete imported source-time initialization plans
for `Lean.Elab.Frontend`, then execute that module plan before calling them.
The file-local plan has zero actions. Source-time initialization installs global
extension descriptors and builtin handler closures; it does not import logical
constants into each newly created `Lean.Environment`.

To reproduce the bundle, use the current native exporter and the pinned sysroot:

```sh
LEAN_SYSROOT="$(lean +leanprover/lean4:v4.33.1 --print-prefix)" LEAN_PATH=target \
  target/lean-ir-export --source lean/HostedFrontendProbe.lean --local HostedFrontendProbe \
  > target/hosted-frontend-probe-source.jsonl
```

The producer is still a native bootstrap tool. The text supplied later to the
exported guest entry must be processed by guest IR; invoking the native producer
on that text would not establish hosted elaboration.

## Native oracle and acceptance order

`target/hosted-frontend-native.log` contains the native probe run. Summary weights
are errors=1, presence of `HostedSort`=10, `hostedValue`=100, `answer`=1000.

| Gate | Entry/input | Native result | What it establishes |
| --- | --- | ---: | --- |
| 1 | `emptyEnvironmentSummary` | 0 | Guest environment plus initial extension states |
| 2 | `processSummary ""` | 0 | Exact incremental frontend entry and terminal command |
| 3 | `processSummary "namespace Hosted\nend Hosted\n"` | 0 | Builtin command elaboration and scopes |
| 4 | `processSummary "axiom HostedSort : Sort 1\n"` | 10 | First strict kernel admission and publication |
| 5 | Previous axiom followed by `axiom hostedValue : HostedSort` | 110 | Persistent environment lookup/admission across commands |
| 6 | `set_option autoImplicit false\naxiom hostedValue : UnknownType\n` | 1 | Diagnostics collected from snapshots |
| 7 | Unseeded polymorphic identity definition | 1001 | Negative test: declaration presence does not imply compilation |
| 8 | `elaborateAndRunSeededIdentity 42` | 42 | Minimal positive compile/evaluate/apply target |

There is also `synchronousProcessSummary`, using the original
`Lean.Elab.Frontend.processCommands : FrontendM Unit` in the same pinned source.
It is a legitimate smaller command-loop gate, not the acceptance substitute for
`Lean.Elab.process`: native bad-type and unseeded-identity observations return
0 and 1000 respectively because diagnostics can live in snapshot tasks that this
raw loop does not collect. The exact incremental path returns 1 and 1001.

## No native environment object is needed to start

`Lean.mkEmptyEnvironment` (`Lean/Environment.lean:1530`) checks that initialization
has finished, runs `EnvExtension.mkInitialExtStates`, and constructs ordinary
Lean data. The extension constructor traverses registered descriptors and calls
each `mkInitial` guest closure (`:1377`). Its kernel constants start as
`SMap.empty.switch`; the async checked view is a `Task` containing kernel data.
This is already compatible with the guest heap/closure model. Do not replace it
with an opaque pointer to a native Lean environment.

Builtin command elaborators are initialized via `commandElabAttribute`
(`Lean/Elab/Command.lean:407`) and stored as values. Their builtin registration
does not require importing the entire logical constant environment to elaborate
empty input, namespaces, or the two simple axioms above.

## Kernel callback required by the first declarations

The first normal elaboration callback is:

| Extern | Raw argument types and ownership | Result |
| --- | --- | --- |
| `lean_elab_add_decl` | owned `object` environment, `usize` maxHeartbeats, `usize` maxRecDepth, borrowed `tobject` declaration, borrowed `tobject` optional cancellation token | `object` = `Except Kernel.Exception Environment` |
| `lean_add_decl` | same shape, but first argument is a **Kernel.Environment** | `Except Kernel.Exception Kernel.Environment` |

`Lean.Environment.addDeclCore` calls the first variant, then updates both async
constant maps itself (`Lean/Environment.lean:687–733`). The pinned C++ bridge
strictly checks the declaration and invokes
`lean_elab_environment_update_base_after_kernel_add`; retain this publication
sequence rather than inventing an alternate guest environment shape.

`lean_kernel_check`, `lean_kernel_whnf`, and `lean_kernel_is_def_eq` are separate
Kernel debugging APIs. They are not automatically required merely by creating
an environment or adding the first axiom. If encountered they must be supported
or trap; do not install success stubs. Neither unchecked-add variant should be
used as a fallback for unsupported Java checking.

`lean/KernelBridgeShim.lean` now supplies:

- `checkedKernelRoot` (borrowed Environment → owned Kernel.Environment).
- `checkedEnvironmentIsEmpty` (borrowed Environment → raw UInt8 Bool), checking
  **both** imported `SMap.map₁` and local `SMap.map₂`, with quotient
  initialization still disabled.
- `postCheckSafeAxiom` (owned Environment, borrowed Declaration → Except),
  preserving duplicate detection and rejecting unsafe axioms.
- Existing `postCheckSafeDefinition` with its original closed/safe/single-def scope.

Native binary oracle `target/kernel-bridge-shim-native.log` checks empty versus
imported environments, exact native/shim safe-axiom ConstantInfo equality,
unchanged original environment, duplicate/unsafe rejection, and existing strict
definition admission. Its source-local IR is
`target/kernel-bridge-shim-source.jsonl`. These post-check helpers **do not check**
declarations; only invoke them after Java admission of the identical guest input.

### Persistent Java association

Store associations in snapshot/world context, not a process-global mutable
registry: checked guest Kernel.Environment identity → immutable Java `Env`.
A new, unassociated root may start at `(Env.)` only after the guest emptiness
helper proves the checked constants empty and quotient initialization disabled; an unknown nonempty root must fail.

An ID-only cache without ownership is unsafe: the IR runtime can reuse a unique
constructor and mutate its fields while preserving its Ref ID. Retain an owned
reference to each associated **kernel root** for as long as the association is
cached. That anchor prevents uniqueness-based mutation of the cached root and
its reachable immutable constant map. Keep the anchor and Java Env together in
the snapshot; a world fork copies both. Explicit pruning can release old anchors
later. Do not derive Java state from an unrelated session-global environment.

For admission, resolve the guest root, obtain its associated Java Env, strictly
project/check the declaration, run the appropriate guest post-check helper,
then resolve and anchor the returned checked root with the returned new Java Env
before resuming guest code. If any stage fails, do not publish a clean successful
association. Extensions remain guest-owned; Java only represents the corresponding
kernel declarations/quotient state. `Env.addConstant`/TypeChecker admission return
persistent Java environments; their shared lookup cache is not a mutable logical
constant store.

## Exact frontend tasks need dependency semantics

`Lean.Elab.process` (`Lean/Elab/Frontend.lean:134`) calls `IO.processCommands`,
which calls `IO.processCommandsIncrementally`, then
`Lean.Language.Lean.processCommands`. The latter immediately creates a promise,
a cancellation token, and starts `process.parseCmd` with `sync := true`.
The snapshot pipeline creates further promises before resolving all of them.

Upcoming raw extern family from the collected pinned producer:

| Extern | Raw arguments | Result |
| --- | --- | --- |
| `lean_io_as_task` | erased, owned callback object, owned priority tobject, void | Task object |
| `lean_io_map_task` | erased, erased, owned callback object, owned task object, owned priority tobject, uint8 sync, void | Task object |
| `lean_io_bind_task` | erased, erased, owned task object, owned callback object, owned priority tobject, uint8 sync, void | Task object |
| `lean_io_promise_new` | erased, erased Nonempty, void | promise tobject |
| `lean_io_promise_resolve` | erased, owned value tobject, borrowed promise tobject, void | tagged Unit |
| `lean_io_promise_result_opt` | erased, borrowed promise tobject | Task object |
| `lean_option_get_or_block` | erased, erased Nonempty, owned option tobject | tobject |
| `lean_io_check_canceled` | void | uint8 Bool |

A deterministic scheduler can avoid host threads, but unresolved promises must
remain unresolved and callbacks must run when their dependencies permit.
Treating every task as already complete, running every waiting callback eagerly,
or substituting arbitrary defaults for blocked values can deadlock or silently
change elaboration. Snapshot/fuel/fork state must include pending closures,
owners, dependencies, promise resolution and cancellation state. Resolution is
first-write-wins; dropping an unresolved promise resolves its optional result to
None. Existing pure Task/get/map support is only a subset of this protocol.

## Minimal compile-and-call environment

The unseeded identity definition typechecks and is present in the returned env,
but compilation reports `Unknown constant lcAny`; native `evalConst` then reports
unknown declaration `answer`. Empty kernel state is therefore not sufficient for
execution even for an otherwise closed polymorphic identity.

A native positive experiment succeeds with exactly these declarations from
pinned `Init/Prelude.lean:27–33`:

| Name | Level parameters | Type | isUnsafe |
| --- | --- | --- | --- |
| `lcAny` | [] | Expr.sort (Level.succ Level.zero) | true |
| `lcErased` | [] | same | true |
| `lcVoid` | [] | same | true |

`compilerMarkerEnvironment` admits them through ordinary strict native kernel
checking. `elaborateAndRunSeededIdentity` then elaborates
`def answer.{u} (α : Sort u) (x : α) : α := x`, obtains the compiled value, and
returns its input (native 42 → 42). General unsafe axiom admission remains
forbidden by `postCheckSafeAxiom`. The separate `admit-compiler-marker` /
`postCheckCompilerMarker` pair now admits only these exact raw declarations.
`kernel-host/make-binding` requires the explicit `:allow-compiler-markers? true`
capability and its `:compiler-marker` trusted helper; both are disabled/unneeded
by default. Raw mdata-wrapped or normalized max/imax equivalents, namespace
prefixes, extra level parameters, wrong names/types and missing unsafe metadata
are rejected. Java admission still calls TypeChecker.checkConstant and preserves
the unsafe flag; no unchecked insertion or general unsafe-axiom policy is used.

Native IR observations (`target/hosted-frontend-diagnostic.log`):

```text
def answer (x_1 : ◾) (x_2 : @& tobj) : tobj :=
  inc x_2;
  ret x_2

def answer._boxed (x_1 : tobj) (x_2 : tobj) : tobj :=
  let x_3 : tobj := answer x_1 x_2;
  dec x_2;
  ret x_3
```

The erased type still occupies a runtime argument slot. The unsafe probe uses
`evalConst (Unit → Nat → Nat)` and supplies Unit to that ignored slot; it does
not pretend that this is the declaration's original dependent Lean type.
The raw interop API must similarly use explicit erased/unboxed ABI descriptors.

After elaboration, new optimized IR lives in the guest environment extension
`Lean.IR.declMapExt`, not automatically in the JVM runner's `:functions` map.
Use `Lean.IR.findEnvDecl` or the exported `lean_ir_find_env_decl` /
`lean_ir_find_env_decl_boxed` helpers to fetch it; get the actual boxed wrapper
when present, then feed structurally decoded declarations into the existing
lowerer/linker. Install the new function map in the snapshot and matching runner
program before returning a guest closure from `lean_eval_const`.

Pinned `lean_eval_const` returns **Except**, not IO.Result: error tag0/string,
success tag1/value (`src/library/ir_interpreter.cpp`). It evaluates a constant
with zero supplied arguments: for arity > 0, allocate an owned zero-capture
closure using the actual boxed declaration when available. Do not invoke the
strict direct-call API with zero arguments or route this through apply_n(0),
which is invalid. For arity 0, load/cache the actual constant, box its raw IR
return type, and return an owned result. This includes initialized values;
allocating a closure for every constant would be wrong. Existing closure saturation now provides the
application mechanics once the proper code/value has been installed. Preserve
`evalCheckMeta` behavior when enabled; this probe explicitly sets checkMeta=false
and does not establish general module/meta compatibility.

## Boundary after this experiment

The three compiler-marker axioms establish a small compile-and-call gate.
Ordinary `Nat`, inductive declarations, imported tactics and Mathlib additionally
need coherent guest logical constants and persistent extension import state.
Running source-time module initialization alone does not load those constants;
reusing the host native environment would hide this missing layer. A later
import bridge must transfer verified logical declarations and extension entries,
or faithfully implement the relevant .olean import protocol. The current
one-way Java projection, single-def checker and tiny seed do not establish that.
LLVM is unnecessary for these gates: the existing guest IR/JVM backend can run
the resulting functions once the frontend and dynamic-code installation work.

## Runtime IR handoff helper

`lean/RuntimeCompileShim.lean` adds a guest-executable handoff, without changing
or rebuilding `Export.lean`:

```text
exportCompiled : Lean.Environment → Array Lean.Name → IO String
seededIdentityBundle : IO String
```

The first serializes the actual supplied environment's optimized IR to the
existing structural JSONL schema. The second builds the three-marker seed,
elaborates the identity with exact `Lean.Elab.process`, checks diagnostics, and
returns its IR bundle **without** evaluating the new constant. It is the next
native-to-JVM import oracle, then a guest-to-JVM dynamic installation target.

The bundle preserves structured names, borrowed parameter flags, full IR types,
all FnBody alternatives, closure/direct-call dependencies, initializer targets,
closed/ground/value roles, and source-order initialization actions from LCNF's
impure declaration indices. Entry points explicitly identify an existing boxed
wrapper; an absent boxed wrapper is not fabricated. It traverses dependencies
until closed or missing, reports missing names explicitly, and exports available
Lean-defined extern alias metadata only when the target has an actual fdecl.
Imported bodies may still be unavailable in the supplied environment; the host
must satisfy such names from its coherent existing catalogue or reject linkage.

The initialization plan is scoped to **all local declarations in that environment**,
not a delta since the last handoff. Installing a second bundle must not repeat
source IO effects already executed by `lean_run_init`/prior initialization.
Identity has no local init actions, making this ownership/publication issue
independent of the first compile-and-call test.

Dynamic install must reject overwriting trusted static runtime, kernel helper,
and handoff helper function keys. Empty logical environments can permit a user
to declare a same-named helper even though its trusted implementation already
exists in the host execution program. Name-only invocation without that protection
would undermine the host's post-check trust boundary.

Validated after the memory pause:

- The seeded frontend native oracle returns 42, and the real kernel-shim native
  binary passes. The quotient-aware kernel shim source-local artifact has been
  re-exported and verified (`target/kernel-bridge-shim-source.jsonl`, 102 declarations).
- `RuntimeCompileShim.seededIdentityBundle` runs natively and returns a manifest
  plus exactly two fresh declarations, `answer` and `answer._boxed`, with no
  missing dependencies or local initialization actions
  (`target/runtime-compile-identity.jsonl`). It never calls the fresh definition.
- The existing Clojure importer loads those two declarations and executes their
  actual emitted IR on reference, mutable, eager JVM and lazy JVM backends.
  All pause budgets 0 through 7 agree; the Nat result is 42. A reference argument
  returns with its single owner intact, exercising the emitted borrowed
  argument retain/release sequence (`target/runtime-compile-jvm-oracle.log`).

The runtime shim's own source-local IR export is also complete:
`target/runtime-compile-shim-source.jsonl` contains 363 declarations and no
local initialization actions. Executing the entire frontend/compiler inside the
guest is a separate integration gate still in progress.


Compiler-marker capability validation: `target/compiler-marker-validation.log`
passes 18 JVM tests / 178 assertions across projection, strict checking, host
capability isolation and ownership. `target/compiler-marker-native.log` validates
all three exact native marker values, duplicates and nearby invalid names/types/
parameters/flags, alongside previous safe-axiom/definition checks. The refreshed
kernel shim artifact includes `postCheckCompilerMarker`. The native canary now
links against the pinned shared Lean runtime (`KernelBridgeShim-native-shared`,
85KB executable), avoiding a second 221MB statically linked copy during experiments.


Current assembly boundary: the [full Init assembly experiment](../measurements/full-init-assembly.json)
passed with authenticated lazy ModuleData, explicit initializer capabilities,
and the rebuilt kernel classes. It covers 631 module records and returns owned
assembly roots, not a finalized or checked Environment. Finalization, strict
association, ordinary resident adoption and durable checkpoints remain separate
work. The next bounded performance comparison forks the same prepared input
through mutable and demand-compiled JVM execution before attempting the long
finalizer again.

The next bundle-generation draft also needs lossless native Name identities.
The [native-name evidence record](../measurements/native-name-evidence.json)
captures a pinned Init inventory of 65,994 distinct Names, including quoted
macro names which cannot all use Java display strings as native identifiers.
The isolated draft reader retained every identity and matched 3,775 candidate
ConstantInfo Names by structural equality. Planning found 40 missing metadata
roots; the selected legacy metadata gate accepted 1,338 identities. These are
research observations, not a promoted bundle: serialization must translate every
selected global field, and declaration tags, safety, axiom completeness and
native expression-equality obligations remain mandatory independent gates.


A [standalone exact native root preflight](../measurements/exact-root-native-preflight.json)
now has positive and negative native evidence. The pinned helper accepted all 40
missing metadata roots plus Nat and the quoted macro identity. It rejected a
Nat spelling paired with Bool's identity, and a missing exact root. Four pure
protocol tests also passed. The [helper](../scripts/validate_bundle_roots_v2.lean)
and [harness](../scripts/exact_root_preflight.py) use a bounded structured request,
explicit pinned sysroot and captured input hashes; they never invoke the exporter.
This fills an experimental naming check, not declaration validation or bundle
finalization. Concrete generator wiring and all other strict gates remain open.
