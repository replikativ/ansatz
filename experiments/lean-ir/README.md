# Lean IR runtime REPL experiment

An isolated Ansatz experiment, outside the library's normal source/AOT paths.
The branch is `experiment/lean-ir-runtime`, based on the numeric fixes in PR #116.
No public runtime API or package split is decided here.

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

The JVM machine suite passes 8 tests / 37 assertions; the Node runner passes
14 checks. The optional SCI bridge passes 1 test / 5 assertions. Native Lean's
list oracle returns `[2, 3, 4, 5]`, matching the imported guest execution.
The surrounding Ansatz source and AOT JAR suites each pass 713 tests / 2417 assertions using
an empty optional store root and the required medium Init fixture. Full Init and
Mathlib fixtures were not provisioned in this worktree. The experiment namespaces
are absent from the production AOT JAR.

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
module and a separately packaged portable runtime possible. Decide after the next
vertical slice: native exporter to guest execution, then an explicit ABI for kernel
and runtime services. Code generation and guarded specialization can share that ABI.

## SCI world integration

The optional adapter uses the same released SCI version pinned by Simmis:

```sh
clojure -Srepro -J-Xmx1g -M:sci
```

It stores a suspended guest state in an SCI-created atom, forks the SCI context
between evaluations, and resumes the children to different results. The parent
and each child's simulated resource events remain isolated. The host `guest/resume`
function runs the machine directly; SCI does not interpret each guest instruction.
The machine's explicit frames supply guest continuations, not SCI or JVM stack capture.

This is an in-memory integration check, not a durable snapshot codec. Ordinary
SCI forks do not capture an active dynamic binding frame; asynchronous integration
must explicitly convey and retarget the SCI continuation context. Forking from
inside an active evaluation of that same source world is unsupported.

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
