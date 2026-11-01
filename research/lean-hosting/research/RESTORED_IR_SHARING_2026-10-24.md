# Restored Lean IR: REPL memory investigation

This follows the [compact-memory investigation](COMPACT_HOST_MEMORY_2026-10-24.md).
It measures representations and introduces a restore optimization; it does not
establish public Project loading or full-frontend fit in a smaller heap.

## What was measured

A live REPL ran with a 384 MiB heap, Java Instrumentation object sizing and JFR.
The uncompressed 610 MB checkpoint was scanned and fully hashed without loading
its data graph. Deterministic uniform reservoirs and largest-frame cohorts were
kept separate. The larger uniform sample contains 4,096 of 334,467 function rows.

The existing representation has four distinct layers:

| Layer | Representation | Finding or action |
| --- | --- | --- |
| Executable IR | Function maps containing nested ordinary vectors, e.g. `[:let ...]` and `[:return ...]` | Vector objects, backing arrays and Name strings dominate the sampled function graph; function maps are a small part. |
| Structured Names | Shared prefix vectors such as `["str" prefix component]` | Prefix sharing already exists, but separate canonical Names still retain duplicate tag/component Strings. |
| Guest state | Persistent heap maps containing node maps, fields, RC and layout/scalar storage | Measured separately; not changed by this optimization. |
| Checking projection | Java names, levels, expressions, constants and projector tables | Separate from executable IR; earlier full checking pressure remains unresolved until another complete run. |

In the initial 256-function sample, body data contained 6,102 distinct String
objects representing 838 values. The Name marker `"str"` alone occupied 2,846
String objects. Function maps were much smaller than the nested vectors, backing
arrays and Strings they referenced. This justified sharing before a class rewrite.

The production normalizer comparison gave:

| 4,096-function sample | Existing Name sharing | Fused sharing |
| --- | ---: | ---: |
| Reachable object bytes | 22,350,008 | 13,892,480 |
| Reachable objects | 712,024 | 410,004 |
| Median fresh read/decode/normalize time | 427.66 ms | 466.70 ms |
| Median current-thread allocated bytes | 445,388,512 | 504,538,112 |

That is **37.84% less reachable object size**, with about **9.1% more time** and
**13.3% more allocation** in five alternating paired trials after two warmups per
mode. These timings concern initial sample admission, not evaluator throughput.
The graph measurement sums exact VM shallow sizes over distinct reachable
objects. It excludes static fields and is not a dominator retained-heap analysis.
Do not extrapolate it into a promised full-frontend saving.

## Change and memory semantics

The restorer fuses two pools into its already required exact Name-normalization
walk: Strings belonging to eligible metadata-free Names, and metadata-free
`[:var Long]` operands with IDs 0 through 4095. The operand pool applies only
inside the `:body` of an exact function row. Literal/immediate payloads, direct
targets, metadata and non-code rows do not acquire operand context. Other numeric
types and IDs outside the pool range retain their representation.

All pools are local to one parse and are cleared in `finally`. There is no global
intern table. Clearing a pool does not mutate the vectors/Strings returned to the
World. Persistent snapshots and forks therefore share ordinary immutable data as
before; separate restores do not acquire shared executable authority. The same
function map still enters world, prepared and imported registries. Refs, guest
heap objects, RC counts, native sources, class inventories and wire formats are
unchanged. Baseline `checkpoint_wire.clj` remains unchanged.

Custom immutable classes remain an option if profiling the remaining vectors
justifies them. They would need the existing collection, metadata, wire and width
proof contracts. Mutable objects require ownership/COW integration with retained
Worlds. This experiment supplies no evidence that replacing function maps with
classes is the right next optimization.

## Validation and limits

- **80 tests / 24,096 assertions passed**, covering checkpoint encoding,
  restoration, strict fixture checking, authority/cleanup and normalization.
- All 4,096 actual sampled function rows retained identical checkpoint bytes.
- Three-backend original/shared/original executions agreed, and literal,
  metadata, numeric-boundary, malformed-row, registry-identity and separate-parse
  controls passed. The permanent optional test runner includes the new suite.
- Focused validation used a 384 MiB heap and peaked at 520,654,848-byte group RSS;
  all 462 input hashes matched afterward and the process was disposed. The live
  profiling REPL also exited normally with all 275 initial pins matching.
- An initial validation harness exposed five provenance scripts by placing the
  entire captured-consumer directory on its classpath. Existing tests caught it.
  The corrected harness exposes the unchanged 48 Java class files plus ordinary
  source roots; no assertion was weakened. The failed attempt is preserved.

JFR also sampled substantial allocations under decode and `wire-value` validation.
That validation reconstructs a temporary transformed tree which decode then
discards. A non-reconstructing validator is a separate candidate requiring full
rejection/metadata/float compatibility tests. The recording includes REPL graph
analysis and encoding trials; its weights are not one production restore's
allocation totals and do not establish live retention.

See [scalar/class evidence](../measurements/restored-ir-sharing.json) and the
[reproducible profiling helpers](profiling/README.md). No new full Init restore,
65,994-constant strict check or public P1 acceptance was run with this change.
The modified restorer requires a fresh externally accepted consumer digest before
another complete campaign; the old c036 identity remains historical.
