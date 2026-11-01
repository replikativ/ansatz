# Bulk execution probes after primitive loop repair

All iterations reused the existing 384 MiB REPL. The workload is the pinned,
native-exported RBMap closure, not a project load, kernel admission, frontend,
Init restore or Mathlib check. Each run builds and folds a fresh tree. Complete
final Worlds, including logical RC, heap, registers, counters and result, are
compared against the persistent reference outside the measured interval.

## What was tested

| Variant, n300 | Thread allocation | Median CPU | Decision |
| --- | ---: | ---: | --- |
| Ordinary direct-call routing | 39.58 MB | 34.9 ms | Baseline for direct-call trial |
| Omit direct-call application map | 38.93 MB | 34.6 ms | About 1.7% allocation saving; not promoted |
| Dense join captures | 39.58 MB | 31.4 ms | Baseline for sparse trial |
| Sparse join captures | 37.23 MB | 42.2 ms | About 6% saving, 34% CPU regression; not promoted |

The timings in different experiments are not interchangeable baselines. JVM
tiering, scoped redefinitions and machine conditions affect timing. Alternating
variant order and seven paired samples reduce, but do not remove, those effects.

The n100 join probe counted 2,535 captures of 131-slot arrays. Only 8, 10, 17 or
19 slots were bound in each capture; the others contained the unbound sentinel.
Sparse storage therefore looked promising. The prototype captured all bindings,
including nil and dead diagnostic registers, into owned compact arrays and
expanded them only at a jump. Full World parity passed at n11, n100 and n300.
However, scanning, packing and restoring did not repay their cost on this
workload. It is not a new production representation.

The direct-call prototype preserved closure routing and the ordering of caller
frame publication, function resolution and arity errors. Its small benefit did
not justify adding another production call path. Full completed-World parity is
the bounded evidence here; exhaustive failure/fuel acceptance was not attempted
for either rejected variant.

## Validation and lookup overhead

Allocation samples had pointed to scalar layout checks and native-reference
lookups as well as call/join arrays. A scoped identity cache found just seven
immutable layout identities despite repeated validation. These further controls
used the same program and input, with seven alternating-order samples:

| Control, n300 | Thread allocation | Median CPU |
| --- | ---: | ---: |
| Unmodified helpers | 39.59 MB | 48.3 ms |
| Cached successful layout validation | 32.15 MB | 44.5 ms |
| Native-import lookup without get-in sequence | 35.70 MB | 46.2 ms |
| Both cached validation and lookup change | 28.26 MB | 42.1 ms |
| Stateless direct layout predicates | 34.45 MB | 46.5 ms |
| Stateless predicates plus lookup change | 30.56 MB | 44.1 ms |

The retained implementation uses the last approach. It recovers most of the
allocation saving without a validation cache, new ownership rules, private
representation or stale-proof invalidation policy:

- `scalar/layout!` checks the same three fields directly rather than building
  a vector and sequence for `every?`. Predicate order, accepted integer types,
  limits, errors and identity return remain unchanged.
- Native-reference membership and imported-node lookup use nested keyword
  access instead of constructing traversal sequences. Top-level import
  precedence, nested fallback, membership/lookup and shadow checks remain intact.

The paired experiment reduced allocation by approximately 23%. A subsequent
run of the actual changed source measured about 29.3 MB for private compiled
n300, versus roughly 39.6 MB in the earlier source. This is confirmation of an
allocation reduction, not a clean additional speedup ratio: method generations,
warmup and ordering differ. Updated CPU remained about 49.5 ms. Generic bulk
execution still needs substantial improvement.

## Reproduce and inspect

[Recorded measurements](../measurements/bulk-execution-probes.edn) contain all
samples, join shapes/density, decisions and focused test totals. Allocation is
current-thread allocated bytes, not retained heap. Preparation is excluded.

Start with the [feasibility helpers](runtime-feasibility.clj), then load:

```clojure
(load-file "research/bulk-calls.clj")
(bulk-calls/benchmark ctx 300)
(load-file "research/bulk-layouts.clj")
(bulk-layouts/benchmark ctx 300)
;; The sparse trial temporarily redefines compiler/runtime internals.
;; Use only in an otherwise idle research REPL; return frozen Worlds only.
(load-file "research/bulk-sparse-joins.clj")
(bulk-sparse-joins/check-pure!)
(load-file "research/bulk-sparse-compiler.clj")
(bulk-sparse-compiler/benchmark ctx [11 100 300])
```

The helper baselines are the functions currently installed when the probe
starts. Reproducing the original before/after numbers requires the original
source revision; running against the retained source does not reconstruct an
old baseline. Rejected controls are retained as research evidence, not public
runtime entrypoints or shipped optimizations.

Sparse storage uses a reload-stable JDK carrier and a persistent research marker.
It owns its data, retains no entry-register array, performs no logical RC
operations, and preserves capture-before-materialization ordering. Its runtime
adapter supports dense captures too and conservatively declines unchanged-host
storage reuse. The compiler variant has a separate generation to prevent cache
mixing. These scoped redefinitions must not overlap other interpreter work;
private Machines must be frozen before leaving the scope.

## Verification and campaign consequence

Scalar layout tests now cover missing/malformed fields, bounds, oversized Long
values before arithmetic overflow and accepted BigInt layouts. Existing tests
exercise uninitialized bytes, aliases, imported heaps, COW, every-fuel behavior
and forks. In the retained REPL, 44 runtime tests / 3,310 assertions and all 91
optional compiler tests / 23,794 assertions passed. Independent review found no
blocking semantic issue; CLJS runtime execution was not independently tested.
The fresh component gate includes the scalar storage test explicitly.

Final fresh-class component validation passed: 73 infrastructure tests / 1,064
assertions, 15 runtime/storage tests / 244 assertions, 25 branching tests / 459
assertions, 16 metadata tests and the isolated legacy namespace-load check.

The primitive-loop fix is now merged as PR232. Selected-project examples remain
the release objective. Full hosted/image runs stay parked: these bulk results
do not justify extrapolating a fast frontend.

The next structural target is compilation that retains more work across small
heap-reading/scalar callees, plus prepared scalar-access facts. This should
avoid generic dispatch, repeated validation and frame materialization, rather
than pack the current frames more elaborately. It must preserve exact
fuel/error behavior, logical RC, snapshots and imported-resource boundaries;
the existing interpreter remains the differential oracle. Near-native speed
and a complete new heap representation are not prerequisites for the next
bounded experiment.
