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
