# Java Lean IR interpreter baseline

This is a research port of the execution model in Lean
[`819816b2`'s C++ interpreter](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/ir_interpreter.cpp).
It executes the original typed exported IR. It is separate from the existing
World interpreters, compiler and optional Lean facade; it is not a released
backend or complete Lean runtime. The port carries the upstream Apache license.

The purpose is to establish competitive interpreter execution before introducing
forkable storage. No guest-specific JVM compilation, Pattern or LLVM is used.

The [explicit continuation experiment](CONTINUATIONS.md) adds a second mode with
instruction-boundary pause/resume. Recursive execution remains the control/default;
the heap is still mutable and neither mode is forkable.

## Representation

- Immutable prepared functions and instruction nodes resolve calls and supported
  externs once. Names and persistent source maps stay outside the execution loop.
- Reusable object and primitive stacks use function base offsets. Join declarations
  store code pointers; jumps bind parameters in the current activation. There is
  no register-environment capture at a lexical join.
- Java nodes contain tag, logical RC, object fields and packed scalar bytes.
  Unique stores mutate nodes directly. Logical decrements release child edges;
  shell deletion transfers children without decrementing them. Java GC manages
  physical allocation. Register copies do not acquire guest ownership.
- Internal constant loads borrow cache-owned values. External nullary calls
  acquire an owned return reference; closing the engine drops cache ownership.
  This follows the pinned producer, whose constant ownership differs from the
  older sibling checkout. Constants are not automatically made immortal.
- Ordinary calls recurse through the Java interpreter. Self-tail calls move
  arguments through reusable scratch slots and reset the function PC. The
  explicit driver provides instruction boundaries; the
  [eager fork oracle](../JAVA_EAGER_FORK.md) copies its control and graph.
  Class loaders isolate REPL engine generations.

The implementation precomputes frame sizes and resolves function/intrinsic
identities, whereas upstream grows slots on access and caches symbol lookup.
Object and primitive stacks replace its C++ union. Eight Nat intrinsics have
Java implementations rather than a native boxed ABI bridge. These are explicit
JVM adaptations, not a binary Lean runtime ABI.

## Bounded profile

Supported value lanes are object/tagged/tobject/erased/void, uint8, uint32 and
64-bit usize. The [scalar extension](../JAVA_SCALAR_RUNTIME.md) specifies host
unsigned carriers, boxing, packed fields and bounded raw-IR limits. The profile
covers constructors, object/byte projection and stores, calls, boxed partial and
closure application, boxing/unboxing, literals, sharing tests, RC operations,
joins, cases, returns and traps. Nat add/sub/mul/div/mod/pow/equality/less-than support
nonnegative Long and promoted BigInteger values. Subtraction saturates; mod0
returns the numerator. External uint8 inputs require exact values in 0..255.

Preparation checks unique binders, lexical scope, physical lanes, call/jump arity,
extern backend precedence/signatures and the supported type profile. It does not
grant kernel checking or source-admission authority. Inputs are trusted exported
declaration sets, not a public source-file loader. Stack/index preparation remains
bounded by the prototype's limits; arbitrary deeply nested input is unverified.

Unsupported families include floats, uint16/uint64, struct/union,
reset/reuse, foreign functions outside the captured runtime profile, real host IO,
tasks/resources, native globals/initializers and the full string/MPZ object runtime.
String and large-Nat arithmetic leaves use JVM values without guest RC headers;
sharing tests and object cases on those families reject. The prototype does not
enforce upstream RC persistent assertion flags, matching the pinned interpreter's
ordinary inc/dec behavior. It has a call/self-loop budget and interruption polls,
not the legacy World's exact instruction-fuel/checkpoint ABI.

The eager fork is an explicit O(capacity + reachable graph) research operation;
cheap branch versions and managed cancellation remain planned. The engine is
not thread safe, reentrant through the external entry, or compatible with arbitrary
World handlers. `invoke` is an internal typed owned-argument entry,
not Lean's general `call_boxed` or the public Ansatz interop API. Callers release
owned node results with `dec`; closing an engine releases its cache, not outstanding
caller ownership. Closures pin their code image and reject another image.

## Validation

The bounded suite exercises cache borrowing/sharing/close, packed offsets beyond
the first scalar word, shell deletion, captured/shared closures and overapplication,
Nat promotion/zero rules, invalid profiles, self-tail argument permutations, stack
growth, code-image isolation and external byte input errors. It also compares:

- Complete intermediate RBMap tree tags, fields and scalar bytes, then completed
  fold results at sizes 0, 1, 11, 100, 300 and 1000.
- All 81 MCMC constructor-data declarations against the persistent reference,
  twice each to cover cold/warm cache access. This does not execute a sampler.

The baseline suite has nine tests and 258 assertions, including guest allocation
and field-store counter parity at every RBMap size. The current runner executes it
in both modes and adds eight continuation tests: 26 executions / 1,331 assertions.
The tests run from a separately compiled
jar in a fresh 384 MiB JVM and are part of the experimental CI contract job.
Six additional [compatibility inventory tests](corpus-checks.clj) add 38
assertions for pinned fixtures, static dependency derivation, dynamic-site
reporting and rejection of hash/name/producer drift. The runner now executes 32
tests / 1,369 assertions before the extern expansion. Five further
[extern tests](extern-checks.clj), run in both modes, bring the current runner to
42 executions / 2,711 assertions. The
[extern ABI and Nat report](../JAVA_EXTERN_RUNTIME.md) records native oracles,
signature validation and remaining gaps. These tests do not execute original
RBMap `main`. Six more [scalar tests](scalar-checks.clj) run in both modes,
bringing the current isolated gate to 54 executions / 3,776 assertions.
The [original main runtime slice](../JAVA_RBMAP_MAIN_RUNTIME.md) adds strings,
arrays, virtual captured stdout and iterative release. Its nine tests in both
modes bring the gate to 72 executions / 4,117 assertions. Panic default behavior
and several stream operations remain explicit unsupported paths; this is not
general IO or hosted file-loading acceptance.
The [closed provider](../JAVA_PURE_PROVIDER.md) and fork checks bring the bounded
runner to 109 executions / 10,908 assertions. A separate
[genuine source run](../JAVA_GENUINE_SOURCE_RESULTS.md) uses the hosted frontend;
the small runner does not restore Init or run full Mathlib.
Runtime/compiler defaults and the optional package source inventory are unchanged.

## Measured baseline

Java 25.0.1, Clojure 1.12.4, 384 MiB heap. Fresh bounded processes warm one engine,
then take seven batches of 100 executions at alternating inputs 1000/1001. The
same Lean harness takes seven batches of 100 with native preference disabled.
Both paths verify checksum 10,050. Clocks below exclude startup/preparation.

| RBMap build and fold | Thread CPU per run | Wall per run | Thread allocation per run |
| --- | ---: | ---: | ---: |
| Java port, ordinary HotSpot C2 | 4.734 ms | 6.160 ms | 1.516 MB |
| Java port, default JVMCI compiler | 2.766 ms | 2.818 ms | 1.516 MB |
| Lean 4.33.1, IR preferred | not measured | 4.505 ms | not measured |

The C2 port is competitive in scale, about 1.37 times the Lean wall time in these
samples; the default JVMCI route is about 1.6 times faster. The machine was shared
and busy, without affinity; Java CPU/wall differences and sequential process
measurements limit precise ratios. Host-JVM compilation is present in both Java
paths; neither emits guest-specific code. This is not a general Lean benchmark.

At inputs 300/301, wall medians are C2 1.179 ms, default JVMCI 0.692 ms, and Lean
0.859 ms. Native externs remain enabled in Lean's IR-preferred route. The previously
measured optimized native executable was about 0.184 ms at 1000/1001, still much
faster than this interpreter; its older receipt is separate from these fresh runs.

The prior generic compiler measured about 120 ms CPU and 119 MB allocation at
input 1000. It also materializes a final World, so this is diagnostic context,
not a pure isolated backend ratio. The structural interpreter change closes most
of that observed gap, without establishing the cost of forkable storage.

First preparation of the 15 raw declarations took 13.75 ms CPU and 2.09 MB
allocation in the fresh default process, excluding JSON reading. Seven retained
REPL samples after ten preparation warmups had a 3.15 ms CPU median. Preparation
and JVM startup are excluded from hot execution. The fresh measurement records,
native rows, source pins and limits are in
[java-ir-baseline.edn](../../measurements/java-ir-baseline.edn).

## Reproduction

From `experiments/lean-ir`, resolve the normal experiment dependency basis once.
Compile this engine separately from production classes:

```sh
mkdir -p target/java-ir-baseline/classes
javac --release 11 -g -d target/java-ir-baseline/classes \
  research/java-ir-baseline/src/ansatz/research/ir/Interpreter.java
jar cf target/java-ir-baseline/interpreter.jar -C target/java-ir-baseline/classes .
clojure -J-Xmx384m -J-Xss8m -M research/java-ir-baseline/check-runner.clj \
  target/java-ir-baseline/interpreter.jar
clojure -J-Xmx384m -J-Xss8m -M research/java-ir-baseline/benchmark-runner.clj \
  target/java-ir-baseline/interpreter.jar target/java-ir-baseline/measurement.edn
```

For a retained REPL, load `unchanged-program-benchmark.clj`, then `repl.clj`.
`class-basis` accepts a class directory or jar. Recompile changed engine classes
to a new directory and open a new basis; keep existing Machine classes loaded.

`native-harness-tail.lean` appends a timed batch harness to the exact original
`test/fixtures/unchanged-programs/rbmap.lean`, renaming its original main only.
Both native and Java batches alternate n/n+1 to prevent loop-invariant hoisting,
verify checksums and report seven samples. Native timers exclude frontend startup
and compilation. Java preparation is measured separately, excluding JSON reading;
execution uses a warmed retained engine, not final World materialization.

With `LEAN_BASELINE_BIN` set to an existing pinned Lean 4.33.1 `bin` directory:

```sh
clojure -M research/java-ir-baseline/write-native-harness.clj \
  target/java-ir-baseline/RBMapBench.lean
"$LEAN_BASELINE_BIN/lean" --version
"$LEAN_BASELINE_BIN/lean" -Dinterpreter.prefer_native=false --run \
  target/java-ir-baseline/RBMapBench.lean 1000 100
```

This disables preference for precompiled functions; extern primitives still use
Lean's native runtime. It is not a wholly native-free execution mode.

The next experiment adds forkable heap ownership over explicit continuations,
measuring each storage change against the recursive control. Guest RC, JVM storage
ownership and external resource authority remain separate contracts.

The [Expr/Level scalar data tranche](../JAVA_EXPRESSION_DATA_RUNTIME.md) adds
exact original computed-data extern tuples and boxed wrappers. Its focused tests
cover native cache-word packing and U64 pauses/forks; this adds no AST storage
representation.

The [checked-disabled profiling callback](../JAVA_PROFILE_RUNTIME.md) executes
the original option getter, retires the native declaration owner before the
callback, and preserves explicit code/host/fork control. Enabled profiling and
inactive/recursive execution remain outside that opt-in profile.

The [borrowed checking projection](../JAVA_KERNEL_CARRIER_PROJECTION.md) reuses
the existing kernel bridge with invocation-local Java Node storage views. It
adds no engine or guest AST representation and preserves explicit ownership.

The [resumable Expr.find profile](../JAVA_EXPR_FIND_RUNTIME.md) runs original
owned wrappers over borrowed source Expr graphs in active explicit mode. It
preserves callback traversal/sharing policy, code/Host/fork pauses and pending
cleanup continuations without adding traversal owner credits.

The [Void.mk release unit](../JAVA_VOID_RUNTIME.md) consumes the original owned
payload before returning void zero, including resumable finalizer cleanup in the
active runtime and checked quiet release in inactive modes.

The [structural Level equality value unit](../JAVA_LEVEL_EQUALITY_RUNTIME.md)
exposes the existing bounded Level comparator through exact borrowed
`lean_level_eq` and its original owned boxed wrapper. Together with Level.mkData,
it covers the two externs in pinned Lean/Level.lean; universe equivalence remains
outside this binding.
