# Runtime feasibility before expanding project loading

These probes run in one retained 384 MiB Java 25 REPL. They load selected,
already-exported Lean IR, not a frontend, Init image, Source or Mathlib. The
purpose is to identify a manageable performance path before repeating the
project-loading campaign. No native-speed or whole-project claim follows.

## Heap-heavy execution is still expensive

The original pinned Lean RBMap workload builds a tree and traverses it to count
selected values. One retained program is warmed eight times at n100; five
trials at each size alternate backend order. Complete final Worlds are compared
outside timing, including logical RC and all guest counters. Preparation is
excluded; fresh state, execution and final materialization are included.

Median results for 300 inserts plus traversal:

| Execution path | Current-thread CPU | Allocated bytes |
| --- | ---: | ---: |
| Persistent reference | 152.7 ms | 224.9 MB |
| Mutable | 66.3 ms | 57.1 MB |
| Compiled regions | 53.8 ms | 39.8 MB |
| Compiled, private between build and traversal | 52.4 ms | 39.6 MB |

Avoiding the intermediate snapshot saves only about 143 KB here. Boundary
materialization therefore does not explain the bulk allocation. Recent
interop-heavy improvements cannot be extrapolated to this workload.

Platform baselines insert the same keys/values and count the same selected
entries: Clojure's sorted map took about 0.13 ms / 163 KB, and Java TreeMap about
0.07 ms / 20 KB. These use different implementations and ownership guarantees,
so they are platform controls, not exact Lean/JVM speed ratios. They show that
the current cost is not imposed by the JVM itself.

Instrumenting an n100 execution separately, outside timing, observed 3,091
guest calls, 893 releases, 863 retains and 1,110 scalar extern operations. This
is a call/heap-heavy test. Samples and source inspection identify register/join
arrays, generic runtime dispatch, node lookups, RC handling, argument vectors
and scalar validation as candidates. The samples do not establish a single
dominant source that would justify replacing the entire heap representation.

## A concrete typed compiler defect

The typed scalar worker was intended to have primitive long lanes. Compiler
reflection/boxed-math diagnostics and JFR instead found a reflective
`longValue` receiver followed by boxed arithmetic in the generated loop.

The receiver is a generated `case` form. A hint on the unquote or on that macro
form does not establish the required type after expansion. The fix binds its
result to a generated local carrying the `java.lang.Number` tag and invokes
`Number.longValue` on that local. The compiler can then infer primitive loop
lanes. Calling Clojure's checked `long` coercion directly would be wrong for
unsigned BigInt values above Long/MAX_VALUE; the existing low-bit conversion
must remain intact.

The generated loop's arithmetic, fuel accounting, carrier recipes and snapshot
contract are unchanged. The new regression test forces fresh compilation with
reflection warnings enabled. Existing tests check high-bit UInt64 values,
wraparound, carrier-preserving snapshots, Nat overflow fallback, caller frames,
and fuel/quantum boundaries.

One retained typed program, seven samples per size:

| Sum loop length | Allocation before | Allocation after |
| --- | ---: | ---: |
| 100 | 49.4 KB | 35.8 KB |
| 1,000 | 92.0 KB | 35.8 KB |
| 10,000 | 562.2 KB | 63.4 KB |
| 50,000 | 2,673.4 KB | 201.6 KB |

The flat allocation below one execution quantum is encouraging. Above it, the
existing worker returns through materialization/guards every 4,096 iterations;
that is a likely source of residual growth, not a fully isolated attribution.
The measured interval includes entry checks, initial state, thaw, execution and
freeze. It is not a bare native loop measurement.

At 50,000 iterations observed median CPU changed from about 5.2 ms to 1.8 ms.
Different generated methods and sequential warmup/JVM tiering limit that timing
comparison. The allocation change and disappearance of reflective entry and
boxed lane arithmetic are stronger evidence than the timing ratio. A Clojure
primitive sum loop is included as a control, not a claim of native parity.

Replacing max helpers alone, and attaching the receiver hint directly to the
macro form, did not remove the allocation slope. Those variants were discarded.
Remaining boxed-math diagnostics in generic fuel subtraction occur in the
fallback path; arbitrary-size fuel values must not be narrowed without proof.

## Reproduce and inspect

[runtime-feasibility.clj](runtime-feasibility.clj) contains bounded REPL helpers:

```clojure
(load-file "research/unchanged-program-benchmark.clj")
(load-file "research/runtime-feasibility.clj")
(def ctx (runtime-feasibility/setup))
(runtime-feasibility/benchmark ctx [11 100 300] 5)
(runtime-feasibility/profile! ctx :jvm-private 300 10 "target/runtime-feasibility/tree.jfr")
;; Optional Pattern compiler path:
(load-file "research/typed-tail-benchmark.clj")
(runtime-feasibility/typed-scaling)
```

The [measurement record](../measurements/runtime-feasibility.edn) preserves
CPU/allocation counters, scope, operation counts and sampled stack summaries.
JFR recordings stay under ignored target output. One sample weight exceeded
the entire measured allocation window by orders of magnitude. It is preserved
as an attribution outlier rather than assigned to this workload. JFR weights
can carry sampler state outside the measured interval; remaining weights are
diagnostic, not exact allocation percentages or retained-heap sizes. Profiled
timings are perturbed and are not mixed with unprofiled timing results.

The existing optional compiler lane now contains 91 tests; all 23,794 assertions
passed in the retained REPL. A final 384 MiB fresh-process check also passed all
91 tests / 23,794 assertions using the retained dependency basis (including
Pattern 1.0.452). The CLI-pinned Git dependency check stopped before tests because
the shared Git cache was read-only; repository CI remains the pinned-basis gate.
Independent source review found no correctness blocker in the
type-inference fix or its unsigned-carrier semantics.

## Campaign consequence

The typed path has a concrete, improvable implementation, but heap-heavy generic
execution remains too expensive to declare project performance acceptable.
Do not start another full image merely because the scalar loop improved.

The next bounded experiment should remove substantial ordinary-call or private
node overhead on this same small RBMap workload. Compare direct-call entry,
join/frame materialization and private node headers separately, preserving the
reference backend, snapshots, logical RC and failure behavior. Attempt one
structural change at a time; retain only changes with measured benefit. A new
general runtime or mature JIT is not a prerequisite for these probes.

Once representative execution improves, measure one small actual source load
in a retained frontend session, with restore/check, imports, elaboration,
compilation, publication and invocation timed separately. Selected project
examples remain the release goal; native parity is not an admission criterion.
