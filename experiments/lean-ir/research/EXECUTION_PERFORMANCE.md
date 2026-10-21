# Execution mode comparison, 2026-10-20

The current runtime is far from competitive with compiled native Lean on these
heap kernels. [Raw measurements, source hashes and guard results](../measurements/execution-modes-oct20.json)
retain fresh runs on the same Intel Core Ultra 7 258V and Oracle JDK 25.0.1.
Each case uses 20 warmups and 11 timed samples; the restricted numeric compiler
uses 200 warmups. These exploratory medians have substantial variance and no CPU
isolation or confidence intervals.

For mapping a 1,000-element unique list:

| Mode | Median | Relative to native C-AOT | Relative to default Lean `--run` |
| --- | ---: | ---: | ---: |
| Lean C backend, `leanc -O2` | 0.0071 ms | 1× | — |
| Lean `--run`, default native fallback | 0.189 ms | 26.6× | 1× |
| Lean `--run`, native preference disabled | 0.300 ms | 42.2× | 1.59× |
| Persistent reference machine | 51.81 ms | 7,290× | 274× |
| Mutable machine | 12.54 ms | 1,765× | 66× |
| Eager JVM blocks | 8.36 ms | 1,176× | 44× |
| Eager blocks, static runtime calls | 11.31 ms | 1,592× | 60× |

This does not establish small backend rankings. Across map/fold/reverse/mirror,
the eager block medians are roughly 710–3,823 times their native C baselines;
reverse is especially noisy and slower than mutable in this run. Native Lean
also specializes/replaces some library code, including mapTR. These are
equivalent-kernel implementation comparisons, not identical-IR compiler tests.

`--run` invokes Lean's IR interpreter while preferring available native symbols.
The additional `-Dinterpreter.prefer_native=false` run disables that preference;
extern and initializer native lookup still applies. Reverse illustrates the
difference: default `--run` takes 0.0049 ms, while disabling native preference
takes 0.123 ms. There is no universal "Lean interpreter slowdown" factor.

The closed numeric subset is much closer to native: 20,000 mutual tail transfers
take 0.0483 ms through the numeric JVM compiler versus 0.0102 ms for native
UInt64, about 4.75×. The mutable interpreter takes 39.70 ms and persistent takes
106.98 ms. Native `--run` takes 7.22 ms for Nat and 9.45 ms for UInt64.
The numeric subset guards exact small integers; it is neither general arbitrary
precision Nat compilation nor interchangeable with modular UInt64 semantics.

Kernel timers exclude input construction, JVM thaw/freeze, result checks and
process/frontend startup. JVM GC can occur inside a timed region, whereas native
result destruction occurs after its clock read. Native allocation was not
measured. The heap benchmark uses eager block compilation, not adaptive resident
`:jvm` execution.

For iteration, one guest IR callback edit rebuilds one block, reuses twenty and
returns its checked result in a 2.94 ms median, including restore/execute/freeze.
That excludes Lean parsing, elaboration, kernel admission and IR export. Numeric
compilation has a 6.61 ms repeat median; rebuilding the complete 21-block heap
program takes 82.34 ms. Native build timings cover a different whole module and
linking task, so they do not supply a compiler-latency ratio.

The accepted full frontend campaign currently uses **`:mutable`**. Its actual
fresh typed-profile Init+A finalizer took 1,061.63 seconds; separate strict
checking of 65,995 constants took 177.49 seconds. There is no matched native frontend baseline for that
profile, so a full-frontend slowdown ratio remains unmeasured. The next performance
comparison should restore the same prepared profile and inputs across mutable
and adaptive JVM execution, separating cold compilation, warmed code-cache reuse,
source processing, import reconstruction and Java kernel checking. That follows
the now-passed source-import witness correctness gate.

The separate [Oct21 prelude fork experiment](../measurements/prelude-semantic-forks.json)
completed two actual A revisions, identical B compilation/imports, Nat/Unicode
calls and a retained old-B call in 31.619 seconds. That aggregate excludes runtime
restoration and seed preparation; the guarded process lifecycle was 340.96
seconds. The frontend and finalizer used mutable execution. Only admitted output
calls used a shared JVM cache: A1 compiled five blocks; A2 compiled one and reused
four. This proves cache reuse and fork correctness for the observed case, rather
than a per-file latency distribution or a matched native performance result.

Reproduction uses the existing `bench.py` and `heap_bench.py` harnesses with a
fresh output directory. Native-interpreter rows run their `lean/Bench.lean` and
`lean/HeapBench.lean` programs through pinned Lean 4.33.1 `--run`, once normally
and once with `-Dinterpreter.prefer_native=false`, using the same workload,
warmup/sample arguments and internal timers. All three guarded runs exited zero;
all native checksums and JVM reference-equality checks passed.

## Next checkpoint: resident source iteration

Measure restoration/certification once, then repeat actual source edits on
independent forks of one authenticated prelude context. Keep the fresh-process
correctness gate separate from steady-state iteration. The public frontend finish
operation can separate guest compilation from FILE installation without compiling
the source twice; a profiling controller must retain the actual raw result and
preserve the production ownership sequence.

Record encoding, guest compiler work, FILE decoding/lowering/installation,
publication, import assembly, finalization/checking and calls separately. Include
guest-step deltas, GC counters, program/heap sizes and compiled/cache-hit counts.
Nested helper timings need explicit nesting; summing inclusive parent and child
measurements would count work twice. Sampling or a separately identified JFR run
can examine costs inside public boundaries without redefining trusted functions.

The source review identifies candidates to measure, rather than established
bottlenecks:

- Resident readiness rediscovers selected transitive closures; publication checks
  readiness before compilation, afterward and during adoption.
- `raw/open-functions` scans every function for raw-extern ABI compatibility,
  including when opening a mutable session. Installation and host-link paths can
  reopen sessions.
- `mutable/thaw` consults `slot-count/program-slots`. Its program cache holds one
  weak map identity, so alternating different branch maps can repeat aggregate
  width reductions. Individual function widths already have weak caching.
- Heap overlays already reuse attested persistent bases and freeze dirty nodes.
  A thaw does not necessarily copy or scan the complete heap. Distinguish cold
  proof checks, changed nodes, globals and continuation restoration.

If measurements implicate these costs, first consider a warm resident context,
reusable independently authenticated closure descriptions, ABI validation cached
by exact immutable code/binding identities, or bounded weak program-width hints.
If guest execution dominates instead, select hot compiler helpers for tiering.
Demand-program creation itself does not eagerly JIT the whole frontend.

Any change must preserve old-fork results, unit/function/receipt identities,
explicit binding authority, compiler-token compatibility, checked Environment
associations and independent root ownership. Performance hints grant no checking
authority. Changes to core runtime semantics require an explicit producer/consumer
compatibility contract; they cannot relabel the old checkpoint's build identity.

## Oct21 warm public workflow

The [warm-stage receipt](../measurements/resident-import-warm-profile.json)
records two warmups and three measured trials on independent forks of the same
checked prelude Context. Both public consumers execute the genuine hosted
frontend and import finalizer using mutable execution. Alternating A bodies
produce the expected 42/43 and Unicode results through identical B source.
All 30 trial-created Contexts close successfully; the borrowed base stays
unchanged. No source initializers run.

| Public operation | Median of three measured trials |
| --- | ---: |
| Fork | 10.469 ms |
| Compile and publish A | 6,015.828 ms |
| Prepare and freshly check A's import | 4,114.891 ms |
| Compile B | 5,130.871 ms |
| Nat call | 364.016 ms |
| Unicode call | 71.507 ms |

These are public-operation timings, excluding restoration and seed preparation.
The sample is small; JVM heap/GC observations span controller bookkeeping and
are process-wide, whereas guest steps and guest allocations refer to the actual
branch. Heap differences do not measure total allocated bytes. There is no
matched native frontend baseline. The unprofiled baseline has no active JFR
recording; a separate one-trial CPU profile can investigate the costs above.

Each Nat/Unicode call executes eight guest instructions and allocates zero guest
heap nodes. The Nat call's hundreds of milliseconds therefore justify examining
host setup, closure validation, session opening and slot sizing before changing
guest dispatch or attempting a wholesale frontend JIT. This is a hypothesis from
operation boundaries, pending stack-sample attribution.

The separate [CPU-profiled trial](../measurements/resident-import-cpu-profile.json)
also passes, closes its six created Contexts and closes/dumps its JFR recording.
Its configured settings enable CPU/native method samples and GC events, without
allocation events. Samples are JVM-wide; analysis selects the actual recorded
workflow thread. The 32 MiB retention setting does not bound native memory or RSS.
The shared guarded JVM subsequently exits zero without a guard stop, at a
3,590,819,840-byte peak RSS. Its 1,362.85-second lifecycle includes idle REPL time
and all three campaigns; it is not an operation latency.


Offline analysis selects 1,640 Java execution samples from the workflow thread;
all 878 native-method samples belong to the REPL main thread and are excluded.
Exclusive first-match attribution finds 458 thaw/freeze samples, 107 slot-sizing,
55 readiness, 13 session ABI scans, 113 other, and 894 broad guest runtime samples.
The last category includes runtime helpers and persistent-map construction; it
is not a dispatch-loop cost measurement. Of the selected traces, 298 are
truncated by JFR. Counts are observed stack attribution across the whole trial,
not per-stage latency or wall-time shares. The absence of checker-frame hits does not establish
negligible checking cost.

This supports two focused experiments: avoid rebuilding unchanged boundary state
(particularly the globals conversion in `thaw`/`freeze`) and reuse scalar slot
widths across exact immutable program identities. The broad runtime samples also
justify investigating repeated adapter-map construction in `runtime-value!`.
Keep authority validation unchanged while testing these representation changes,
then rerun the same fork/import/call workload. ABI scans and readiness traversal
remain measurable candidates, but this trial does not make them the dominant
whole-workflow cost. A core implementation change requires a new authenticated
runtime identity and an explicit checkpoint compatibility decision.


A separate offline refinement of the same immutable recording localizes 288 of
the 458 thaw/freeze-category samples to `freeze` line 226 (globals to persistent
map), and 145 to `thaw` line 217 (globals to HashMap), using the nearest observed
application frame. These are not self-time measurements; JVM frames can appear
above that application frame. The overlapping function-presence counts include only nine
`freeze-heap` and thirteen `thaw-heap` samples. This strengthens the case for
measuring a globals base-plus-delta representation first. Within the broad guest
runtime category, 582 samples contain `runtime-value!` and 452 contain the
primitive evaluator; these overlapping counts must not be summed. All capture
and attribution limitations above still apply.

The globals experiment must preserve the current Java HashMap key relation.
Direct persistent-map lookup/association can treat numeric keys or nested name
segments differently (for example boxed Integer versus Long); globals also use
synthetic IO-key vectors. Reuse an equality-preserving overlay or retain a
conservative conversion fallback for unsupported maps. Preserve initializing,
recursive initialization, IO success/error and reference-ownership behavior, as
well as independent fork snapshots. Performance hints must not change checking
or binding authority.
