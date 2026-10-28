# Klara / Lean branching contract experiment

This is a bounded executable experiment, not a production resource API or an
interpreter refinement proof. A separate small pure model now has checked
theorems; see the [five-step results](KLARA_BRANCH_RESULTS.md). This changes
neither Lean execution semantics nor resident frontend
interop. Klara source is read only by an optional probe; no Klara files change.

## State and authority

Represent inspectable branch data separately as `(definition basis, guest
World, optional branch-local host-cell store, pending intents)`. The guest World
already contains heap, globals and
explicit continuation state. Executable caches and private mutable machines
remain outside this data. The definition basis is an opaque pinned root here:
the experiment does not yet resolve Klara definitions from Lean.

A trusted session provisions one **synthetic family adoption right**. Its
registry is outside guest snapshots. Handles select registered branch state;
copying a handle or an old snapshot does not recreate spent rights in that
session. Provisioning another session explicitly grants another independent
right. The registry is a host atom exposed to trusted experimental callers;
this is neither an unforgeable capability API nor protection against hostile
host code. The runner is trusted too.

The operational rules are:

1. `fork!` consumes an open handle and returns two alternative handles sharing
   immutable branch data. Neither child inherits writable storage. The parent
   snapshot remains readable if retained by its caller, but its handle cannot
   advance again.
2. `advance!` consumes a handle, resumes at a guest safe point, and publishes a
   successor. Persistent interpretation, private mutable execution and
   demand-compiled execution must produce equal Worlds and outboxes. This lab
   uses a fixed 10,000-step budget per runner call.
3. Only scalar `:lab/emit` requests can become deferred intents. They receive
   the fixed speculative acknowledgement `0`. Unknown requests, unsupported
   payloads and more than 64 requests per advance fail closed. No host output
   occurs during advance. This is suitable only for effects whose result need
   not depend on actual external execution. The later host-cell adapter adds
   closed `:lab/cell-read` and `:lab/cell-write` descriptors; these operate on a
   branch-local persistent store and execute no external IO.
4. `adopt!` requires a completed guest and no advancing/forking sibling. It
   claims the family before invoking callbacks. At most one alternative in a
   family may commit; the right is a choice among alternatives, **not** two
   independently spendable resource rights. Discarding one branch leaves its
   siblings available.
5. Callback failure makes the family incomplete. Successfully returned
   callback receipts remain recorded. A callback that throws may already have
   effected the outside world; it is not retried. This is at-most-once attempts,
   not durable exactly-once effects, rollback or crash recovery.
6. Runner failure also makes the family incomplete. Concurrent in-flight
   results cannot subsequently publish. No effectful fallback/replay exists.

General authority splitting, RNG streams, budgets, source/native ownership,
tasks, branch merging and multiple independently adoptable children are not
implemented. They require additional explicit policies. In particular, this
family-selection model does not implement every fork structure in Klara RFC
0001. Ordinary Lean `ST.Ref` semantics provide aliases, not native process
snapshots; branch isolation is our hosted execution extension.

## Fixture and observations

[branch_lab.clj](../src/prototype/branch_lab.clj) constructs handwritten machine
IR with a genuine guest `ST.Ref` shared by a direct argument and a closure
capture. The two branches resume with `10` and `20`, update the cell through
`lean_st_ref_set`, invoke the closure using `lean_st_ref_get`, and queue their
own observed value. The original cell stays `0`. Its logical RC has two owners
before branching; physical isolation comes from immutable snapshots and private
copy-on-write storage, not an RC uniqueness claim.

The runtime operations were checked against Lean's `src/runtime/io.cpp`
implementations of `lean_st_ref_get` and `lean_st_ref_set`. The initial fixture is not
frontend-generated Lean, omits final guest lifetime cleanup, and does not test
Lean's multi-threaded native-reference implementation.

The differential observation is the complete returned packet, including guest
heap, control, logical RC, statistics, pinned basis and outbox. The committed
external trace contains only the adopted branch's outbox. Tests cover aliases,
nested forks, stale handles, discard, partial commit, reentry, simultaneous
adoption, competing advances, concurrent failure and rejected host effects.

The optional live Klara probe loads only its `src/klara/world.clj`. It publishes
definition value `1`, pins a fiber, forks a Klara definition world, stores that
basis beside a Lean snapshot, then publishes parent value `2`. Both executed
Lean alternatives retain basis `1`; the Klara child and pinned fiber also stay
on `1`. This demonstrates root composition, not Klara-to-Lean calls or a
refinement proof between the language interpreters.

## Initial REPL validation and measurements

Reuse a small JVM with the experiment's existing `src` and `test` paths:

```clojure
(require 'prototype.branch-lab-test)
(clojure.test/run-tests 'prototype.branch-lab-test)
(load-file "research/klara_branch_probe.clj")
(klara-branch-probe/benchmark 500)
(klara-branch-probe/fork-scaling)
;; Optional; set KLARA_ROOT to the checkout you want to inspect.
(klara-branch-probe/klara-basis-check
  (str (System/getenv "KLARA_ROOT") "/src/klara/world.clj"))
```

[Recorded results](../measurements/klara-branch-probe.edn) came from the existing
384 MiB Java 25 REPL, without JVM restart, Init loading or a full frontend image.
Allocation is current-thread JVM ThreadMXBean allocation, not retained heap.
Five samples of 500 trials followed operation-local warmup; code preparation is
outside timing. Timing is exploratory and sensitive to tiered compilation and
sample ordering.

Median allocation per trial, rounded:

| Backend | Two complete resumes, no ledger | Provision, fork, two complete resumes, adopt |
| --- | ---: | ---: |
| Persistent | 40.4 KB | 49.9 KB |
| Mutable | 83.1 KB | 91.8 KB |
| Demand compiled | 83.5 KB | 92.6 KB |

Each complete resume crosses the deferred request boundary and returns from
the closure. The mutable and compiled adapters restore/materialize snapshots
at these boundaries; they do not use production unchanged-handler storage
reuse. These are deliberately tiny regions, not representative throughput
benchmarks and not a claim that compilation slows down Lean workloads.

Provisioning and forking an **already frozen** snapshot allocated approximately
2,840 bytes with 0, 1,000 and 10,000 extra heap nodes. This supports structural
sharing for this operation; it excludes obtaining the frozen snapshot, later
writes, authority-specific split costs and retained-heap behavior. Sample
median timings ranged from about 0.8 to 1.7 microseconds; the decreasing times
with larger heaps reflect measurement/JIT ordering, not a size advantage.

Validation: 10 new tests / 103 assertions; with existing mutable execution,
field-copying, persistent-snapshot and lazy-runtime suites, 43 tests / 2,238
assertions passed. Independent source review found an initial pending-request
admission hole; it was fixed and regression-tested. The full repository suite,
fresh-JVM packaging and hosted frontend image were not run for this experiment.

## Five-step continuation

The [follow-up experiment](KLARA_BRANCH_RESULTS.md) completed the bounded
versions of the following five gates. They remain broader production
integration goals; this initial checklist records their intended scope.

1. Agree with Klara on observation and authority policies before extracting a
   shared substrate. Keep definition publication, guest store and settlement
   separately named.
2. Attribute resume allocation to thaw, execution and freeze in this same REPL;
   optimize control materialization without weakening existing World handlers.
3. Add explicit branch-aware host cells and effect descriptors through an
   opt-in adapter. Existing arbitrary JVM objects remain shared resources.
4. Add a frontend-generated Lean reference/closure fixture with correct lifetime
   cleanup, then connect it to the existing resident ownership ledger.
5. Formalize the small pure/store transition fragment, followed by the
   authority rules, and check runtime refinement separately from kernel proof
   admission. Klara redefinition must not mutate admitted Lean constants.
