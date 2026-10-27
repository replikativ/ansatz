# Finite mutable frontend and JVM application slice

Status: the finite genuine gate passed on main `01016b2`, including restoration,
fresh checking, hosted A/B files, selected JVM execution, a Clojure callback and
managed disposal. Exact evidence and measured limits are recorded below. Broad
Lean compatibility and efficient loading remain separate, unproven goals.

The profile is `ansatz-producer50f-coherent-jvm-application-consumer/1`; its contract
schema is `ansatz-coherent-jvm-application-contract/1`. Original producer recipe,
checkpoint format, kernel policy and historical frontend consumer profile remain
unchanged. The factory is identity-issued through the new explicit
`make-coherent-jvm-application-factory` constructor. Restore checks exact producer,
consumer, profile and contract identities. Preparation dispatches the actual
Factory profile, without inventing a Project stage for direct resident files.

The serialized application policy is a closed `:composition/:application` map:

- `:execution-roles`: frontend mutable and application JVM, each fuel500,000,000
  and compile threshold1. Java checker fuel is a separate original policy field.
- `:transition`: exactly `[:mutable :jvm]`.
- `:selection-limits`:16 functions,64 descriptors,100,000 fact/preflight work and
 16KiB source files. Existing typed preparation has its separate bounded pass.
- `:corpus`:1–4 rows, each with distinct A/B direct-input IDs, module/entry/worker
  Lean Names, scalar codecs,1–4 explicit calls with A/B expectations and an
  independent ordinary fallback entry. All capture IDs are globally distinct.
- `:callback`: one explicit exact boxed String-to-Nat ABI, argument ownership,
  entry, bounded input, expected UTF-8 byte length and `:utf8-length` controller
  implementation. This belongs to the first corpus row. No serialized host fn.

The exact stage program is:

```clojure
[:fresh-init :graph-helpers :panic :ordinary-helpers :typed-eio
 :cases-on :seal :helper-value :init-prefix
 :load-a :select-a :call-a :callback :load-b :select-b :call-b-a :dispose]
```

`construct!` authenticates inputs and composition only; it acquires no Source and
performs no guest execution/checking. `run!` restores and strictly checks once,
prepares helpers through the existing public controller, initializes the required
emitted helper value once, then builds an independently authorized callback and
pristine Init prefix. Classic implicit Init imports must match that real prefix.
`:defer` is accepted only when the actual admitted initialization plan is empty;
required initialization is an explicit unresolved prerequisite.

Both A and B load on the retained pristine mutable context. Each loaded World is
reopened through public `raw/open-functions` and `resident/adopt-prepared`, under
THE ORIGINAL independent trusted configuration and exact binding objects. The
controller never reconstructs authority from the live executable image. One
explicit code-cache capability is shared by all A/B JVM branches. The public
resident compiler setter changes selection in a new branch and preserves input.

Selection reads the actual admitted worker row first, then only demanded
callee/extern rows from the original catalogue. Bounded facts use M1/M2 and the
real Pattern representation pass; exact installed bodies/wrappers are checked.
No all-Init scan, name-based SUM recognition, protected replacement or new engine
is used. Unsupported worker shapes refuse selected acceptance; they do not become
successful compiled evidence merely because generic execution works.

Boxed calls record actual typed-tail artifact identity AND executor return
`:specialized`. The fallback control runs on the selected JVM context with no
selected-worker events. The typed callback receives immutable values and performs
exactly one effect; this is not nested guest reentry. Loading A/B may not add
callback effects. B must have different source, admitted unit and worker/compiler
keys. A/B/A keeps old A callable; a newly selected old-A program must hit the same
shared cache and execute the same artifact. A wrong-image handle rejects before
encoding, and any unexpected returned owner is still escrowed before failure.

Every Context/prefix result is captured before postconditions, timings or logs.
Known temporary call contexts close after observation; retained version contexts
close in reverse order. Each inherited Init-prefix registry is released through
its existing public capability before its Context closes. Source lease closure
comes last and checks the actual Store's closed flag. Unknown partial operation
or destructive cleanup failure retains canonical escrow and lease; no retry,
rollback fiction or disposal success is synthesized.

Final result top keys are exactly status/disposal/stages, contract/implementation/
profile identities, the frontend execution triple, separate application execution
and `:measurements`. Measurements contain only bounded `:corpus`, `:callback` and
`:phases` scalar data. They retain no World, Context, lease or checking authority.
The17 phase entries use `:stage` in exact order. Restore and strict checking are
separate segments under fresh-init. Shared helper preparation timing is recorded
once and labelled for its other stages; overlapping spans are not summed.
Bounded running messages precede operations. The launcher's new-profile outer
error boundary must print only bounded class/message data, never giant ex-data.

The component [validation record](../measurements/coherent-jvm-slice-components.json)
separates new models, historical source-pin checks and native/data prerequisites.
A fresh source/class/dependency capture, 24-source Java compilation, resource
preflight and genuine A/B load/selected-call/callback/disposal gate subsequently
passed, as recorded below. General Project dependency reload, Mcmc sampling, broader non-tail JIT,
Java facade composition and production deployment are separate gates.


## Current-main genuine acceptance, 2026-10-27

The exact current-main cohort at `01016b20c425b059331b1649abbd5e72170178f7`
passed the full seventeen-stage gate in one fresh JVM. Source-level `entry` and
`identity64` names resolved through admitted manifest boxed targets. Actual hosted
A/B elaboration, the selected worker, String-to-Nat Clojure callback, A/B/A
isolation, shared-cache reuse, wrong-image rejection before encoding, and managed
Context/prefix/Source disposal all passed. This is finite fixture coverage,
not complete Lean/Mathlib compatibility or packaged Java-facade acceptance.

[The receipt](../measurements/genuine-hosted-jvm-main01016.json) and
[verbatim output](../measurements/genuine-hosted-jvm-main01016.stdout) preserve the
exact cohort, launch, limits, phase events and terminal result. Detailed private
corpus results were not printed; value/route/cache statements are supported by
the authenticated controller's mandatory assertions, not reconstructed raw keys.

| Operation | Inclusive wall time |
| --- | ---: |
| Restore checkpoint | 292.15 s |
| Bootstrap support plus fresh strict Init checking/projection/association | 655.81 s |
| Prepare Init prefix | 17.05 s |
| Load A | 50.54 s |
| Select A compiler facts/context | 1.08 s |
| A calls: three selected plus one generic fallback | 2.86 s |
| One Clojure callback | 0.47 s |
| Load B from pristine baseline | 43.94 s |
| Select B | 0.71 s |
| B/A calls plus version/cache controls | 2.87 s |
| Managed disposal | 2.95 s |

The complete guarded process took 1110.34 s, peaked at 3,637,760,000 bytes group
RSS, and kept at least 1,734,909,952 bytes host memory available. Its heap cap was
3 GiB and group RSS cap 4 GiB. G1 used two parallel and one concurrent worker;
no full collection occurred. A preceding Serial attempt restored successfully
but was deliberately stopped with strict checking incomplete after sustained
full-GC pressure. This supports investigating generation layout; it is not a
controlled collector throughput comparison or proof of the minimum heap.

Phase CPU/allocation counters measure the caller thread. Restore delegates work,
so its reported 6 ms CPU/102 KB excludes the restore worker and must not be
interpreted as total restore work. Shared helper preparation spans overlap and
must be counted once. Call phases include validation, codecs, Context retirement
and version controls; they are not primitive-worker throughput benchmarks.

Loading and public-call latency still need substantial improvement. Profile
those boundaries and reuse validated immutable-image facts before attributing
the cost to interpretation. A direct resident load is different from Project
publication/graph loading. Next compatibility gates should expand to unchanged
programs and imports, keeping proof-only/noncomputable modules separate from
executable roots. The unchanged rbmap/Mcmc constructor runtime corpus is prior
native-exported IR evidence; this new hosted-source gate does not turn that
whole corpus into hosted-file acceptance.

## Boundary attribution and staged development

The controller retains completed diagnostic spans separately from the exact
acceptance result: `boundary-measurements` returns bounded scalar records only.
`:resident-call` includes public validation, target resolution, codecs, execution,
result-context creation and owner escrow. It excludes subsequent retirement.
`:context-retirement` contains `:prefix-release-and-close` and
`:original-context-close`. The earlier gate used prefix release/adoption followed
by closing the newly adopted wrapper; its historical timings remain unchanged.
Nested spans overlap;
do not sum them with their parents or the existing phase measurements. Each row
labels caller-thread CPU/allocation explicitly. Missing completion records mean
the operation did not complete; they do not imply zero cost or safe retry.

Cold strict-init is also split into bootstrap support preparation and strict
admission. The latter still includes getter execution, projection, dependency
ordering, Java kernel checking and live association. These two coarse spans do
not yet attribute those individual components. Async restore still requires
separate worker/process accounting.

Staged developer operations retain the actual checked owners in one JVM.
They do not add authenticated bootstrap entrypoints, authorize a different
runtime image, or turn initialization into a passed campaign. Keep the JVM
under the existing memory and lifetime bounds. Inspect only scalar diagnostics;
never print `checkpoint`, whose borrowed contents can include the entire heap.
Do not reload classes or ownership namespaces under live Contexts. A modified
runtime requires a new development epoch; the old immutable acceptance receipts
remain historical evidence.

With an independently captured and verified development cohort, the REPL
sequence is:

```clojure
(slice/initialize! approved)       ; restore/check/prefix exactly once
(slice/prepare-applications!)     ; hosted A load and selection exactly once
(slice/sample-a!)                 ; reviewed A cases; at most four batches
(slice/boundary-measurements)     ; scalar diagnostics only
(slice/continue!)                 ; finite calls/callback/B/A/disposal
```

Sampling accepts no caller-supplied code, target or arguments, supports one
reviewed corpus row, reserves Context ledger space for the finite remainder,
and checks callback effects did not change. These fixed cases were reviewed as
pure; scalar signatures alone do not prove arbitrary Lean code pure. A repeated
stage or exhausted sampling budget rejects before execution. A partial guest
or destructive cleanup failure is terminal and retains its canonical checkpoint.
An initialized session may instead explicitly `dispose!` its known owners.
The original `run!` performs the unchanged one-shot finite gate without samples.

A small REPL control measured the existing captured identity model on the JVM
backend: 50 protected functions, 52 total functions and 6 heap entries. After
20 warm-up calls, 50 independent calls all returned 42. Median public-call wall
time was 0.973 ms, caller CPU 0.948 ms and allocation 63,568 bytes; closing the
returned wrapper took 0.079 ms wall, 0.081 ms CPU and 4,192 bytes. Raw samples
are in `../measurements/boundary-model-control.json`. This model
does not use the genuine frontend, a checked Init prefix or prefix retirement.
It is a small-boundary control, not a Lean worker throughput result or a speedup
against the genuine run. It cannot explain the large-image costs by itself.

The next actual-image measurements must compare first and subsequent pure calls
and their retirement spans before changing validation. The leading narrow
candidate is close-only prefix retirement: existing release makes and validates
a runnable Context that this controller immediately closes. Removing that work
requires preserving exact prefix/Source/anchor checks, registry/root ownership
and terminal partial-failure checkpoints. Immutable code-proof reuse comes only
after that attribution; it must never replace live ownership or image checks.

## Optimize in the small REPL before another full-image run

The full-image experiment is parked. Use the retained small REPL and captured
identity/tiny-prefix fixtures to fix structural costs first. Do not start another
Init restore/check merely because host memory becomes available.

`resident-cost-probe.clj` varies immutable synthetic helper images while keeping
the called identity function unchanged. With 10,000 unrelated functions the
call allocated about 62 KB, as with the small image. When those same functions
became protected dependencies, it allocated 5,889,152 bytes. This isolates the
two repeated protected-registry scans from function execution.

Resident code identity validation now issues an opaque proof after those scans
succeed. Reuse requires the exact function map, binding map, protected-function
map and protected-binding map. Only standard persistent maps with frozen keys
qualify. Unsupported/custom containers retain uncached comparisons. Proof fields
are weak references and the private weak issuer registry holds only booleans;
neither cache retains a World, Context or Source. Reloading the validator starts
a fresh proof epoch. Child contexts inherit a proof when all four maps remain
identical; a changed image takes the full path again.

World/session identity, idle state, live roots and root ownership remain checked
on every use. Unit readiness, boxed entrypoint resolution, dependency closure,
codecs and guest execution retain their existing checks. This proof replaces
only the previous function/binding pointer comparisons, not kernel admission or
dependency validation.

The guarded implementation makes repeated call allocation approximately 38 KB
for all three tested protected sizes: 50, 1,050 and 10,050 functions. First proof
issuance remains proportional to image size (about 5.6 MB for the 10,050 case),
and is recorded separately. Timing varies with REPL redefinition/JIT warmup and
host load; these samples establish the eliminated allocation scaling, not a
general latency guarantee. Before, prototype and guarded results are stored in
`../measurements/resident-cost-{before,prototype,after}.json`. All measurements
use caller-thread JVM counters in a 384 MiB REPL; no full Init is loaded.

These are public boxed API calls including validation/codecs/returned-context
creation. They are not the cost of each Lean-to-Lean call or compiled loop
iteration.

The separate `prefix-cost-probe.clj` uses 17 checked native constants and modeled
guest helpers. It checks exact registry removal, the prefix root's RC/removal,
unchanged input branches and actual Source closure. Five independent baseline
releases per size allocate 346,624 bytes (50 protected functions), 5,217,456 bytes
(1,050) and 51,557,488 bytes (10,050). Inclusive instrumentation at the largest
size attributes about 45.9 MB to three static-closure walks. Preparation checks
and subsequent adoption overlap those walks; they must not be added. Producing
and adopting the context that the caller immediately closes accounts for about
20.7 MB of the release span. Results are in
`../measurements/tiny-prefix-costs.json`. This identifies the next structural
work: closed-branch prefix retirement and reuse of proven frozen static closures.

## Closed-branch retirement and static-closure proofs

The controller now uses `release-prefix-and-close-branch`: release the issued
registry owner, then Environment and Options in a new closed branch. It returns
only a closed receipt and leaves its input/siblings and borrowed Source intact.
It does not create or adopt a runnable Context or invoke kernel getter helpers.
The owner ledger claims the combined operation once and separately closes the
original wrapper where the caller already requested that. Partial failure keeps
the latest available World/session, release phase and completed owner dispositions;
it cannot trigger automatic retry or Source cleanup.

Assert-only readiness reuses two issued static-closure proofs per prefix. These
hold weak references to exact function/registry maps and a bounded frozen root
vector. Immutable map keys and all reachable dependency-bearing structures must
qualify under the existing canonical dependency scanner. Mutable or unsupported
containers take full validation. Metadata-bearing Name spines cannot be cached.
Reloading the proof validator invalidates issuance. Weak identities of the 17
validation/dependency/eligibility rule values also invalidate proofs after partial
REPL redefinitions; changes during validation prevent issuance. No closure map, handler,
Context, Source or World is retained by a proof.

Every use still recomputes binding/configuration roots and checks live ownership,
bindings, manifests, native handlers/signatures, issued prefix membership and the
lower Source/registry/scaffold/anchor/range checks. Ordinary adoption and the
branch-producing `release-prefix` retain their full original paths.

The tiny-Source probe used a 384 MiB REPL. The warm column was remeasured
in a replacement REPL after a server restart, with the final semantic-rule guards:

| Protected functions | Old release/adopt | Closed branch without code reuse | Warm closed branch with proofs |
| --- | ---: | ---: | ---: |
| 50 | 346,624 B | 162,712 B | 83,816 B |
| 1,050 | 5,217,456 B | 3,089,864 B | 83,816 B |
| 10,050 | 51,557,488 B | 30,918,880 B | 83,816 B |

These are caller-thread allocations per retirement, not complete function-call
costs. The new path's first 10,050-function validation still allocated 46,136,680
bytes; image changes or proof invalidation repeat that work. Cold and warm
measurements are separate in `tiny-prefix-retirement-{uncached,cached}.json`.
The probe verifies registry/RC/branch/Source controls. Dedicated tests compare
closed heaps across all three backends, prohibit adoption/guest execution, and
exercise advanced partial-failure checkpoints and warm-cache live-check failures.
No full Init has been loaded to validate these changes.

Final source-load verification in that REPL passed 64 fixture-free models (721
assertions) and 36 focused closure/retirement/controller tests (452 assertions).
These overlapping suites are controls, not a full-image compatibility result.

## Resident target closure reuse

A separate REPL probe puts synthetic static authority dependencies on the
application's boxed entrypoint, keeping its identity-program body unchanged.
This exposes a different graph walk from protected runtime registry validation:
`boxed-entrypoint!` checked the target's transitive executable closure on every
public call. The synthetic dependencies are not guest calls or frontend coverage.

Resident calls now reuse the existing semantic-guarded executable closure proof.
The original three-argument `boxed-entrypoint!` still runs its full checker;
a trusted host assertion arity lets the resident boundary reuse static facts.
Every call still resolves its current manifest target and checks the exact
FileHandle/unit, initialization completion, ABI, codecs, root ownership and
protected runtime bindings/code. Current target roots, code/authorization maps
and validation-rule identities guard every proof use.

A private weak Context-keyed table has one replaceable proof slot per wrapper.
It does not write the exposed owner state Atom or run its watchers. Returned
children inherit a proof seed; forks copy the parent's latest seed. A wrapper
can therefore retain at most its inherited seed and one replacement side proof,
not a history of targets or worlds. Both proofs have only weak code/rule maps
and bounded frozen roots, and cannot retain a Context, Source or World.

The same 384 MiB REPL measured caller-thread allocations per public call,
excluding child retirement:

| Synthetic target dependencies | Before, warm | With proof reuse, warm |
| --- | ---: | ---: |
| 0 | 37,904 B | 44,368 B |
| 1,000 | 1,586,528 B | 44,392 B |
| 10,000 | 15,529,600 B | 44,368 B |

The guards add a small fixed cost for tiny closures while removing proportional
repeated work for large closures. Timing varies with REPL compilation and host
load; allocation scaling is the stronger evidence. Cold validation remains
proportional and the recorded cold samples also include compilation/cache setup.
See `resident-target-probe.clj` (load `resident-cost-probe.clj` first) and
`tiny-resident-target-costs.json` for separate cold/warm measurements.

Six boundary tests (57 assertions) cover same-parent/child/fork reuse across all
three backends, no owner Atom writes, changed current manifest targets,
pending/partial initialization, ABI, roots, protected and application code,
authorization registry identity, semantic-rule changes and weak table values.
The 74-test resident/eval regression run passed 1,026 assertions before the final
two application-code assertions were added; the final focused six tests passed
all 57. No full Init or full-image experiment has been run.
