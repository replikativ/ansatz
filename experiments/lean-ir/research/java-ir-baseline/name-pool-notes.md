# Compact source Header Names

This prototype changes retained Header metadata representation only. Source raw
bytes/SHA, ABI extraction, Header/Function identity, Program generations, kernel
Names, guest Nodes and reference counting are unchanged. Runtime admission still
requires the existing authenticated source adapter; this pool grants no authority.

Each SourceBinding owns one synchronized strong NamePool. CompactName is an
immutable AbstractList/RandomAccess node with tag, prefix, typed leaf and cached
**Java List hashCode**. It has no Source, pool, Program, engine or guest reference.
Prefix nodes and equal String leaves are shared within the source. Another source
has its own nodes; equality remains structural and symmetric with ordinary Lists,
including existing static frozenName lookup keys. Integer/Long/String numeric
leaves remain different keys, as do str/num tags. No normalization is performed.

Only exact anonymous/str/num list spines with immutable supported leaves use compact
nodes. All other Name trees follow the old frozenName copier and original renderer;
existing malformed acceptance/rejection behavior is preserved rather than tightened.
Header exactName and Name-shaped subtrees throughout declaration/evidence metadata
use the same pool, including f, dependencies, sourceModule, redirects, initializer
and extern backend Names. Other metadata retains the recursive unmodifiable List/
Map freezer. All compact-node mutation methods, including empty/no-op bulk methods
and sublists, reject with UnsupportedOperationException.

The lifetime policy intentionally retains canonical names until their SourceBinding
is collected. There is no static/global interner, weak-race duplicate publication,
or eviction that can invalidate sharing. Failed Header issuance may populate this
trusted source's cache, but publishes no Header/Program. Source-only validation is
not a heap-size or throughput acceptance result.

## Verification to run before rollover

Load `name-pool-checks.clj` and call `java-ir-name-pool-checks/check!` with the actual
new isolated basis. Nine families cover canonical sharing across metadata/prefix/
leaves, cross-source and old List equality/hash/map lookup in both directions,
numeric leaf classes/tags, all mutation APIs, mutable caller copies, unchanged
malformed Name behavior, concurrent same-source Header issuance, existing original
CAS Header fixture rows, and original typed key materialization/calls in both
drivers. Existing Header/guest-export/native/source/ABI suites remain necessary.
The standard runner adds this as result group160 with expected9 tests.

`name-pool-benchmark.clj` defines metadata-only `build!`, usable unchanged against
old and candidate Java bases. Supply a bounded lazy sequence of already authenticated
actual CAS `{:row row :sha256 raw-sha}` values, not re-exported metadata or candidate
Names. Use matching row order/count and a scalar source-description. Each call
constructs one Source and retains all issued Headers in its returned benchmark
root. It reports identity-deduplicated metadata graph union by class and source pool
counts; these are NOT exclusive retained sizes. Drop the input sequence and earlier
trial roots before post-GC heap measurement. The returned Headers/Source are model
benchmark roots, not real admitted code receipts. No guest engine/body is built.
Include the source pool's HashMap tables/entries in retained-memory comparison,
not only the Header graph union (the pool is deliberately excluded from that union).

Parent HPROF observation motivating the prototype: 12,268 Header exactName/
declaration/evidence roots reached about179MiB and6.03million objects, excluding
SourceBinding. About695,924 ArrayLists and695,924 wrappers,690,945 arrays and1.58M
Strings/backing byte arrays occurred in that shared union. This is not exclusive
retention attribution and does not predict exact savings. Require original-CAS
old/candidate metadata benchmark, independent source review and full gate before
one binary/new-cohort rollover. Author has launched no JVM or compiler for this unit.
