# Lean IR runtime REPL experiment

An isolated Ansatz experiment, outside the library's normal source/AOT paths.
The branch is `experiment/lean-ir-runtime`, based on the numeric fixes in PR #116.
No public runtime API or package split is decided here.

The JVM experiment now also includes a mutable interpreter, a numeric compiler
and a constructor/closure block compiler. These are experimental alternatives to the portable reference machine,
not changes to Ansatz's production lowering or library runtime.

## Reproduce

From the Ansatz worktree root, compile the Java kernel once:

```sh
clojure -Srepro -T:build javac
cd experiments/lean-ir
clojure -Srepro -J-Xmx1g -M:test
clojure -Srepro -M:nrepl
```

Connect to the printed loopback nREPL port. A plain terminal REPL is also available
with `clojure -Srepro -M:repl`.

```clojure
(require '[ansatz.core :as a]
         '[prototype.examples :as ex]
         '[prototype.machine :as m]
         '[prototype.lean-ir-test]
         '[clojure.test :as t])
(a/init!)
(a/defn ^Nat prototype-inc [^Nat n] (+ n 1))
(= (mapv prototype-inc [1 2 3 4]) (:values (ex/list-demo false)))
(t/run-tests 'prototype.lean-ir-test)
(def lab {:tail (ex/tail-demo 100000)
          :unique (ex/list-demo false)
          :shared (ex/list-demo true)
          :fork (ex/fork-demo)})
(ex/summary)
```

`a/init!` uses the bundled medium tier in trust mode. The DSL definition above is
admitted through Ansatz; comparing its result with the guest is an execution check,
not a proof of correctness of the guest machine.

## What runs

`fixtures/list-map.jsonl` contains actual final Lean 4.33.1 IR exported for
`List.map` and `List.map._redArg`. The importer maps its instruction subset into
explicit register/frame instructions, recognizing a call followed immediately by
return of its result as a tail transfer. It does not substitute Clojure's `map`.

The portable `.cljc` machine executes that program, including joins, dynamic
application, constructor cases/projections, RC and uniqueness-sensitive stores.
The callback is an explicitly limited scalar increment intrinsic. Guest closures
with owned captures are tested separately using a synthetic program.

The mutual tail-call program and `:suspend` instruction are experimental extensions,
not claims that Lean IR already implements multi-shot continuations. A suspended
state includes the guest instruction, locals, join definitions, return frames and
logical heap. Resuming the same immutable snapshot creates independent guest worlds.
References are relative to their explicit guest state and must not be mixed between
unrelated worlds. The prototype does not accept arbitrary host mutable state as a
forkable resource model.

Observed results:

| Case | Result |
| --- | --- |
| 100,000 mutual tail transfers | Result 0; maximum guest return frames 0 |
| Unique four-element list | Mapped values `[2 3 4 5]`; same root identity; four guest allocations total |
| Shared four-element list | Original `[1 2 3 4]` preserved; fresh result; eight guest allocations total |
| Resume one suspended state twice | Results 10 and 20; original snapshot unchanged |
| Resource-bearing closure | Last owner drops its synthetic resource exactly once |

Allocation counters count **guest nodes**, not Java/JavaScript allocations.
Unique stores preserve guest identity but still update persistent host maps.
This is a semantics/inspection prototype, not an allocation-free runtime or a
performance benchmark. Resource finalizers append simulated release events; real
handles, native RC/FFI, threads and external-effect rollback are not implemented.

Guest uniqueness and physical storage uniqueness differ across snapshots. Two
branches can each see guest RC 1 while sharing host storage. Persistent host maps
make the current stores safe. A mutable backend will need world-level ownership,
snapshot copy-on-write or an equivalent guard before turning those stores into raw
host mutation. The tests include forking during non-tail map execution and resuming
both branches through the unique-store path.

Arithmetic intrinsics are intentionally limited to exact small integers within
JavaScript's safe range and reject out-of-range arithmetic. This does not implement
general Lean Nat/Int/UInt64 arithmetic. Scalar constructor layouts, most externs,
boxing, reset/reuse instructions, general partial/overapplication, exception unwinding, module initialization,
kernel adapters and admission-to-executable linking remain unsupported. Unsupported
imported operations fail explicitly. There is no verified compiler or production JIT.

## ClojureScript / Node

The same interpreter core runs on both hosts. The importer/compiler currently runs
on the JVM and emits data; there is no browser-hosted Pattern compiler yet.

```sh
clojure -Srepro -M -e "(require '[prototype.examples :as ex]) (ex/export-portable!)"
clojure -Srepro -J-Xmx1g -M:cljs -m cljs.main \
  -co '{:target :nodejs :output-to "target/portable.js" :output-dir "target/cljs" :optimizations :none}' \
  -c prototype.portable
node target/portable.js
```

The Node runner checks imported map execution/sharing, deep mutual tail calls and
multi-shot state isolation. `package.json` scopes this standalone Node harness as
CommonJS, independent of any containing project's module setting.

## Validation checkpoint

The reference, mutable, numeric-compiler and block-compiler JVM suites together pass
28 tests / 779 assertions (`clojure -M:test`). The Node reference runner passes
17 checks. The optional SCI bridge passes 3 tests / 7 assertions. Native Lean's
list oracle returns `[2, 3, 4, 5]`, matching the imported guest execution.
The surrounding Ansatz source and AOT JAR suites each pass 713 tests / 2417 assertions using
an empty optional store root and the required medium Init fixture. Full Init and
Mathlib fixtures were not provisioned in this worktree. The experiment namespaces
are absent from the production AOT JAR.
The source suite was rerun for the constructor experiment. Production sources and
packaging have not changed; the JAR result is the preceding checkpoint's validation.

## Refresh the native fixture

The checked-in fixture makes the experiment runnable without native Lean. To
refresh it with the explicitly pinned installed toolchain:

```sh
lean +leanprover/lean4:v4.33.1 --run lean/Export.lean --closure Init.Prelude List.map > fixtures/list-map.jsonl
lean +leanprover/lean4:v4.33.1 --run lean/Oracle.lean
```

The exporter and the Lean compiler/runtime are distinct from the guest machine.
Exported algorithm bodies originate in Lean, distributed under Apache-2.0;
the selected producer is Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

## Consolidation boundary

Keep interpreter/ownership semantics separate from JSON import, Ansatz kernel
integration and eventual Pattern nanopasses. That leaves both an internal Ansatz
module and a separately packaged portable runtime possible. The interpreter and
block compiler now share an experimental heap/control ABI. Kernel/native services,
module initialization and admission-to-executable linking remain separate gates
before deciding the package boundary.

## SCI world integration

The optional adapter uses the same released SCI version pinned by Simmis:

```sh
clojure -Srepro -J-Xmx1g -M:sci
```

It stores a suspended guest state in an SCI-created atom, forks the SCI context
between evaluations, and resumes the children to different results. The parent
and each child's simulated resource events remain isolated. The host `guest/resume`
function runs the machine directly; SCI does not interpret each guest instruction.
`(branch-demo :mutable)` restores a private mutable machine for each resume and
freezes its result before returning to SCI; the complete returned snapshots match
the persistent path. No mutable machine is stored in an SCI world cell.
`(branch-demo :blocks)` shares compiled code between the children and returns only
immutable snapshots to SCI. All three execution paths produce equal worlds.
The machine's explicit frames supply guest continuations, not SCI or JVM stack capture.

This is an in-memory integration check, not a durable snapshot codec. Ordinary
SCI forks do not capture an active dynamic binding frame; asynchronous integration
must explicitly convey and retarget the SCI continuation context. Forking from
inside an active evaluation of that same source world is unsupported.

## Mutable execution and baseline compilation

```sh
clojure -Srepro -J-Xmx1g -M -m prototype.mutable-test
clojure -Srepro -J-Xmx1g -M -m prototype.numeric-compile-test
python3 bench.py
```

`prototype.mutable/thaw` restores a reference snapshot into mutable register
arrays, a frame deque, join tables and a heap table with mutable constructor
fields. Tail transfers reuse the current register array. `freeze` copies these
back to the reference representation. Both operations copy live state: there is
no paged copy-on-write implementation yet. A mutable machine belongs to one
execution and must not be accessed concurrently or shared between branches.
Separate `thaw` calls produce independent mutable worlds. RC metadata still
uses small persistent maps, and argument/frame/dispatch operations still allocate.

The tests compare complete reference and mutable states after every instruction
of selected imported and synthetic programs. They cover list reuse/sharing,
closures, resource drops, mutual tail calls and forking with active return frames.
These are differential checks, not a formal refinement proof.

`prototype.numeric-compile/compile-program` translates the numeric tail-only
subset into a Clojure form, which the ordinary Clojure compiler turns into JVM
bytecode. The generated code uses primitive long loop registers and a function
selector for mutual tail transfers. Each arithmetic operation retains the
prototype's exact-small-integer guard. Unsupported heap instructions, callbacks,
joins and suspension reject at compilation; there is no automatic tier promotion,
deoptimization or fallback to arbitrary-precision arithmetic. The generated form
is returned for inspection.

The benchmark compares imported generic `List.map._redArg` on the two interpreters,
a synthetic numeric mutual-tail loop on both interpreters and the numeric compiler,
and equivalent workloads compiled by pinned Lean 4.33.1. Native Lean's map includes
its own specialization and optimized `mapTR` implementation, so this is an
end-to-end execution comparison, not an isolated comparison of heap layouts.
The native Nat loop supports arbitrary precision; a separate native UInt64 loop
provides a bounded-machine-word comparison. Agreement is checked only on the
sampled safe inputs, where all numeric profiles coincide.

Execution timers exclude input construction, mutable restoration and result
inspection. Native IO call boundaries prevent Lean from moving pure work outside
the clock reads; the generated C was inspected for their ordering. The numeric
JVM entry wrapper, argument checks and register preparation are included in its
execution time. Checkpoint timers measure full copying separately. JVM allocation
counts use the current thread's allocation counter and exclude setup; native
allocation is not measured. Native result destruction occurs after the clock read;
JVM GC may occur inside a timed region. No GC suppression or CPU pinning is used.

The runner stores raw samples, toolchain/JVM/CPU details, build/process timings and
source hashes in ignored `target/benchmark.json`. Native Lean is built through its
normal C backend and `leanc -O2`; the run does not compare an LLVM backend.
Cold JVM process time includes namespace loading, setup and every benchmark.
The recorded warm Clojure compile latency is for the small numeric program;
native build timings include the whole Lean benchmark module and linking. They
are different compilation tasks and must not be presented as a compiler speed ratio.

### Retained baseline

[Raw measurements and source hashes](measurements/baseline.json) record one
exploratory run on an Intel Core Ultra 7 258V, OpenJDK 25.0.1 and Clojure 1.12.0.
Times below are medians of 11 samples after 20 warmup invocations; the compiled
numeric loop receives 200 warmup invocations. These are single-process,
single-machine microbenchmarks, with no confidence interval or isolated CPU.

This historical run predates two corrections. `freeze` now explicitly clones
constructor field arrays: `vec` could adopt the old arrays, allowing a continuing
parent to alter a captured snapshot. Native unique-list setup now crosses an IO
boundary, because Lean could move its pure construction inside the clock reads.
Use the newer heap run below for corrected checkpoint and native heap timings;
the historical freeze timing did not establish snapshot isolation.

| Backend | 20,000 numeric tail transfers | Map 1,000 unique nodes | Map 1,000 shared nodes |
| --- | ---: | ---: | ---: |
| Persistent interpreter | 82.93 ms | 23.51 ms | 23.66 ms |
| Mutable interpreter | 32.52 ms | 7.58 ms | 6.58 ms |
| Compiled numeric subset | 0.051 ms | unsupported | unsupported |
| Native Lean Nat | 0.683 ms | 0.0108 ms | 0.0098 ms |
| Native Lean UInt64 | 0.0064 ms | not measured | not measured |

The compiled subset is restricted to exact small integers and rejects overflow;
native Nat is arbitrary precision, while UInt64 wraps outside its range. Their
times describe these implementations on common safe inputs, not interchangeable
numeric semantics. The shared/unique map ordering is noisy and should not be
interpreted as a general advantage of sharing.

The numeric compiler's first invocation took 10.53 ms; repeated compilation of
the small program had a 4.16 ms median. Its timed execution allocated 1,296 host
bytes per invocation, including argument setup; the mutable interpreter allocated
59.2 MB on that loop and the persistent interpreter 163.0 MB. Mutation alone has
not removed boxed values, instruction dispatch, temporary arguments and metadata.
The native module's Lean-to-C and C/link steps took 0.85 s and 1.24 s respectively,
for a different and larger compilation task.

The older path took 4.52 ms to freeze and 4.06 ms to restore 10,000 live nodes and
two return frames. As noted above, it could alias field arrays, so this is not a
valid full-copy snapshot baseline. The heap benchmark below measures the corrected
path. A native allocation or checkpoint comparison is not implemented.

The evidence supports keeping a persistent reference, running private mutable
regions, and compiling useful hot code. It does not establish competitive Lean
frontend execution: the heap workload is still hundreds of times slower than
native, and the compiled numeric example is about eight times slower than the
native word loop. This motivated the constructor and safepoint experiment below.
A cold/edit-to-result benchmark for a growing imported program remains needed.
Keep execution available before hot
regions compile; do not eagerly compile the entire Lean frontend into JVM classes.

## Constructor blocks, snapshots and warm edits

```sh
clojure -Srepro -J-Xmx1g -M:test
clojure -Srepro -J-Xmx1g -M:sci
python3 heap_bench.py
python3 profile_heap.py
```

`prototype.block-compile` emits JVM code for straight-line instructions and case
branches over the mutable runtime ABI. Calls, returns, jumps and explicit
suspension end blocks. Guest return frames remain data; guest calls do not grow
the JVM stack. Constructors, projections, RC, uniqueness-sensitive stores,
closures and joins are supported within the reference instruction subset.

Transfer boundaries expose complete reference states, including guest steps,
ownership counts and return frames. Instruction budgets that end inside a block
use interpreter steps; paused worlds can continue in either tier. This is a
materialized-register baseline, not deoptimization from unboxed native frames.
Snapshots copy all live state; page sharing, asynchronous snapshot requests,
native resources, general externs and exception unwinding remain unsupported.

New fixtures contain actual Lean 4.33.1 IR for `List.foldl`, `List.reverse` and
`HeapProbe.mirror`. The [tree source](lean/HeapProbe.lean) defines a structural
mirror traversal. Tests cover shared/unique nodes, empty inputs, guest closures,
synthetic resource drops, branching, pauses at every tested map instruction budget
and continuing a mutable parent after freezing it. The bounded exact `:add`
primitive supports the fold callback; it is not general Lean Nat addition.

Pass an existing program to `compile-program` when a guest definition changes.
Unchanged blocks are reused. Calls resolve through the machine's function table
rather than inlining callees, so a changed callback does not invalidate callers.
Old programs retain their guest definitions. The cache distinguishes compiler
reload generations and runtime linking options; it is not a durable code cache.

The optional Clojure `:direct-linking` profile links generated blocks to runtime
helpers statically. Guest callees still resolve through the world. Keep the runtime
ABI compatible and reload the block compiler after changing helpers. This profile
did not consistently improve every retained workload and did not materially
reduce allocation.

[Heap measurements](measurements/heap-blocks.json) retain 11 samples after
20 warmups per case on Oracle GraalVM JDK 25.0.1. Lists have 1,000 nodes; the
depth-nine tree has 1,023 nodes. Medians for unique inputs:

| Operation | Persistent | Mutable | JVM blocks | Static runtime calls | Native Lean |
| --- | ---: | ---: | ---: | ---: | ---: |
| Map | 29.73 ms | 25.64 ms | 6.89 ms | 6.06 ms | 0.0081 ms |
| Fold | 24.74 ms | 8.21 ms | 5.09 ms | 4.59 ms | 0.0102 ms |
| Reverse | 12.86 ms | 5.02 ms | 3.17 ms | 3.63 ms | 0.0029 ms |
| Mirror | 10.75 ms | 3.68 ms | 2.85 ms | 3.90 ms | 0.0040 ms |

The matrix runs sequentially in one JVM; JIT compilation, GC and scheduling
affect timings. Modest differences and linking-profile rankings are not established.
Native map also receives Lean's specialization and `mapTR` rewrite. Independent
process forks and sustained-throughput measurements are needed for reliable
rankings. The large native gap is visible across the experiments.

Compiling all 21 blocks for ten guest definitions took 55.3 ms initially and a
74.4 ms median on repeat. Changing increment to decrement rebuilt one block,
reused twenty and returned `[0 1 2 3]` in a 3.33 ms median. This warm IR-edit
measurement includes compilation, restoration, execution, freezing and result
inspection. It excludes Lean parsing/elaboration, kernel admission and IR export.

Corrected full-copy snapshot costs at 10,000 nodes and two return frames were
3.10 ms to freeze and 3.56 ms to restore. The compiled map kernel allocated about
4.0 MB per invocation, versus 29.3 MB for the reference; construction, restoration
and result freezing are outside that kernel timer. Native allocation was not measured.

The [JFR summary](measurements/heap-profile.json) samples 200 compiled map runs.
Object arrays, boxed longs and persistent vectors dominate selected allocation
sample weights. These are not total allocation counts; truncated stacks can be
omitted. Raw recordings stay in `target/`. The next representation experiment
should target compact call frames and live-register spills, joins as control
flow, and Ref-to-map heap indirection. The block compiler retains interpreter
bookkeeping that a closed compiled region should eventually avoid.

### REPL

```clojure
(require '[prototype.heap-examples :as heap]
         '[prototype.block-compile :as blocks]
         '[prototype.mutable :as u]
         '[prototype.machine :as m])
(def functions (heap/functions))
(def code (blocks/compile-program functions))
(def initial (:initial (heap/prepare functions :map [1 2 3 4] false true)))
(def parent (blocks/run! code (u/thaw initial) 20))
(def captured (u/freeze parent))
(def left (u/freeze (blocks/run! code (u/resume! parent nil))))
(def right (u/freeze (blocks/run! code (u/resume! (u/thaw captured) nil))))
(= left right)
```

`prototype.repl/refresh-functions!` refreshes function definitions in already-loaded
machine namespaces while preserving record classes, sentinel objects and resident
values. It intentionally leaves imports, constants and types unchanged. Reload
the block compiler normally to invalidate its cache generation. Do not reload
guest record classes while retaining old values.

Refresh the extra fixtures with the pinned toolchain:

```sh
lean +leanprover/lean4:v4.33.1 --run lean/Export.lean --closure Init.Prelude List.foldl > fixtures/list-fold.jsonl
lean +leanprover/lean4:v4.33.1 --run lean/Export.lean --closure Init.Data.List.Basic List.reverse > fixtures/list-reverse.jsonl
lean +leanprover/lean4:v4.33.1 --root=lean -o target/HeapProbe.olean -c target/HeapProbe.c lean/HeapProbe.lean
LEAN_PATH=target lean +leanprover/lean4:v4.33.1 --run lean/Export.lean --closure HeapProbe HeapProbe.mirror > fixtures/tree-mirror.jsonl
```

## Execution speed and persistence

The persistent machine is a semantic reference and an inspection tool. Competitive
execution requires another representation; translating these map updates literally
into generated bytecode would preserve much of their overhead.

Use mutable register arrays, frame storage and constructor fields between explicit
safepoints. At a checkpoint, seal or copy the live execution state into a world
snapshot. Descendants may share sealed pages; the first write to a page shared with
another world must copy it. Guest RC and world/page ownership remain separate.
SCI already uses dense world-local slots rather than a persistent map update on
every atom write. Its current fork copies allocated slots, so that operation is
not constant time; paging is an optimization to investigate after measuring.

The next tiers should share an explicit runtime ABI:

1. A mutable interpreter, checked against the persistent machine at safepoints.
2. Baseline JVM compilation of blocks, direct calls and loops, retaining explicit
   suspension/deoptimization records at supported boundaries.
3. Guarded specialization of hot regions, with materialization of their live
   state before returning to the general interpreter or taking a snapshot.

Persistence need not be visible on every arithmetic operation. Escape analysis
can keep temporary objects private and unboxed while their region runs. A request
to fork inside such a region must either wait for a safepoint or materialize its
state. Neither arbitrary instant stack capture nor allocation-free snapshots is
provided by this prototype. Native externs and callbacks need defined boundaries.

Benchmark cold startup, warm edit-to-result latency, compilation latency, execution
throughput, host bytes allocated, checkpoint latency and first-write costs separately.
Compare pinned native Lean with the persistent interpreter, a mutable interpreter
and generated code on arithmetic loops, constructor/list reuse, arrays, closures,
tail calls and increasing fork frequency. Include end-to-end elaborator workloads
once the runtime surface exists. The current functional checks establish no speed
ratio or competitive performance claim.

Datahike should hold retained world/code/proof identities, database branch roots
and checkpoint metadata, rather than every register write or RC instruction.
Spindel/Yggdrasil already provide branch and resource policies. A future snapshot
envelope must identify its schema, semantic profile, primitive ABI, program hash,
machine state, database commit roots and effect/resource policy. Durable chunks
need explicit GC roots: IDs hidden inside a serialized blob do not automatically
retain the referenced store objects.

## Formalized Clojure core

Start with an explicit operational core: lexical bindings, strict calls, closures,
conditionals, loop/recur, exact numeric operations and persistent collection
operations. Specify equality/hash, iteration order and numeric behavior instead of
inheriting accidental JVM/JavaScript differences. Add world-relative Vars/ref cells,
dynamic binding frames and explicit effect transitions as a separate layer.
Macro expansion produces this core; arbitrary host interop crosses named primitive
boundaries. Lazy sequences, concurrent state and host exceptions require their own
contracts before admission to the formalized subset.

Lean can specify the core and prove selected passes/refinements. Pattern nanopasses
can implement transformations against it, with differential execution as an early
check. Compiling SCI or checking Ansatz declarations alone does not prove compiler,
runtime, storage or host-interop correctness. The formal specification and backend
refinement proofs remain future work.
