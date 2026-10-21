# Program register sizing experiment

This experiment reduces repeated sizing of large immutable program maps. It has
no frontend performance result yet. The direct host probe in the preceding build
measured roughly 363 ms when alternating two retained programs and a negligible
immediate repeat. That establishes sizing/cache behavior, not call-time attribution.

The global cache now retains at most 16 weak program identities and scalar widths.
It never hashes code, stores a parent/delta chain, or grants executable, source, or
kernel authority. Explicit `(program-slots functions (cache))` retains the original
one-entry cache contract. Live local/frame sizing is unchanged.

`append-functions` constructs the actual program from its base and additions.
Only a previously validated exact base identity, disjoint names, standard maps,
and reusable immutable function graphs permit width propagation. Custom persistent
collections and SubVector views are sized exactly without reusable proofs. Arrays,
ArraySeq, and mutable Java collections retain their rejection. Replacements,
removals, and missing base proofs require exact program sizing on use; an old
maximum cannot incorrectly survive removal of its widest function.

Every final addition is eagerly sized, including malformed trusted lowerer output,
regardless of cache state. This deliberately makes such invalid installations fail
before execution, consistently for cold, warm, and evicted bases. Unexpected
exceptions and resource failures are not swallowed. Normal admission, ABI,
protected-name, initialization, and ownership checks remain independent.

The compiled-unit installer keeps the small final addition map, including global
and IO initializer wrappers after all rewrites. It passes that map to the append
constructor and returns it as `:new-functions`. No arbitrary old/new/width
attestation or metadata hint is accepted. A post-install first call can therefore
reuse a width even when the newly constructed program has never executed.

```mermaid
flowchart TD
  B["Previously sized base: exact identity and width"] --> A["Append constructor builds actual program"]
  D["Final additions, including rewritten wrappers"] --> V["Eager function sizing and validation"]
  V --> A
  A --> Q{"Reusable base and additions; disjoint names?"}
  Q -->|yes| P["Weak new-program identity: max of both widths"]
  Q -->|no| F["Exact program scan on use"]
  P --> T["First thaw: cached program width plus live local width"]
  F --> T
```

The identical synthetic script measures append plus sizing after base validation,
using two warmups and five measured additions in separate 512 MiB JVMs:

| Function count | Original median | Candidate median |
| --- | ---: | ---: |
| 56,125 | 29.28 ms | 0.070 ms |
| 334,755 | 315.69 ms | 0.068 ms |

Cold base validation is excluded from those medians and recorded separately:
627.28 → 704.64 ms and 2,295.53 → 2,442.55 ms respectively. This is synthetic
host sizing, not frontend performance, native Lean parity or an exclusive
attribution of resident call time. The [measurement record](../measurements/program-slot-cache-optimization.json)
contains every sample, source pins, guards and failed development attempts.
Run [the benchmark script](../scripts/program-slot-append-benchmark.clj) under
each corresponding source tree to compare the same workload.

Focused tests cover exact custom-cache behavior, weak retention and eviction,
branch alternation, append propagation, replacement/removal, cache-independent
invalid additions, nested custom views, deep unhashable code, native compiled
fixtures, and final global/IO wrappers. The final focused set passes 62 tests /
1,144 assertions; the complete experimental suite passes 861 tests / 89,557
assertions. A genuine closed constructor probe also passed for the new consumer.
The full archive/frontend run remains a separate gate: its preflight verified
all inputs but did not launch a JVM, because 3,470,368 KiB available memory was
below this experiment's chosen 5,242,880 KiB launch threshold. No actual frontend
speed result is claimed for this candidate.

The candidate's closed restore profile is `/2`, with exactly the reviewed
`slot_count.clj` and `program_install.clj` substitutions in addition to the
previous globals change. Producer recipe and archive bytes remain unchanged;
this is a new consumer identity, not a relabeled producer build. Earlier
validation records describe their explicitly pinned consumer builds.
