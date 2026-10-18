# Parent Ansatz validation

The latest coordinated-bundle/runtime batch passes the complete available non-WIP
source **and rebuilt AOT JAR** suites: **832 tests / 3,653 assertions each**, zero
failures or errors. The independent IR runtime suite passes **721 tests / 60,148
assertions**. Fresh prelude-only facade acceptance also passes against the rebuilt
kernel; ordinary/full-Init facade acceptance remains open. Exact source hashes,
profiles, guard metrics, reviews and remaining work are in the
[coordinated progress record](../measurements/coordinated-bundle-progress.json)
and [actual facade record](../measurements/resident-preparation-progress.json).

The JAR contains all 83 intended AOT namespaces, no dependency classes, and Malli
as source only. Tests exclude project source/classes/resources from their
classpath. Packaged resources match repository bytes; packaged kernel classes
match the rebuild and the actual facade probe. Java rebuild, packaging preflight,
whole-library formatting and relative-link checks pass. Conditional missing-Init
fixture cases and the optional Datahike/uberjar omissions below remain.

The shipped six-resource cohort remains the inventoried legacy bundle. Pinned
4.33 staging checks reached complete CI replay and exact overlap checks, then
failed metadata target closure; no generated replacement was promoted. The pure
per-role planner is implemented, but generation/witness-profile integration and
complete lazy companion activation remain separate gates.

## Earlier hosted source-import partition

The local source and AOT jar checks each pass **602 tests / 2,067 assertions
across 66 namespaces**. This is a bounded partition, not a local full-suite pass.
The [aggregate measurement](../measurements/parent-validation.json) records every
phase, exact namespace coverage, resource limits, source hashes and log hashes.
It complements the experiment's independent
[691-test regression](../measurements/hosted-source-header-regression.json).

| Check | Observed result |
| --- | --- |
| Java rebuild | Passed, 256 MiB JVM heap |
| Successful source partition | 66 namespaces, 602 tests, 2,067 assertions |
| Isolated current Omega at 512 MiB | 19 tests, 147 assertions, one `Java heap space` failure |
| Isolated baseline Omega at `c88f348` | Same 19 tests / 147 assertions and exact failure at 512 MiB |
| `jar-stable` | Passed; both launcher and AOT worker limited to 256 MiB |
| Successful jar partition | Same 66 namespaces, 602 tests, 2,067 assertions |
| Jar Omega | Held before launch: final memory preflight below 2 GiB |
| Six Mathlib namespaces | No successful result; attempts and resource holds below |

The initial source coverage attempted 67 non-Mathlib namespaces: 621 tests /
2,196 assertions, one Omega failure and two sandbox socket errors. The scoped
localhost fetch retry passed 3 tests / 25 assertions, replacing the failed
fetch attempt's 3 tests / 7 assertions. Subtracting Omega and substituting that
retry gives the successful source partition above. Retries are not counted as
additional unique tests. The jar's corresponding partition has exactly the same
assertion count.

The failing Omega case is `corpus-nat-truncated-sub`, for the six-variable
truncated-subtraction contradiction. Current and isolated baseline source both
return `Java heap space` at 512 MiB with identical test counts. The baseline
used its own 19 Java sources, classes, Clojure sources and resources; it did not
replace the current classes or resident REPL. This establishes a pre-existing
failure under these heap limits, not a passing test at a larger heap.

The jar was built from `548db1e9288cf7f49bc3ed27f40358e15b88f239`; its SHA-256 is
`7be3c4178868509e78a44befb49909c31dafc99b7d53c35ac0276f3fcaefe62d`.
The test classpath contained the jar and tests, with project `src`, `classes`
and `resources` directories absent. The jar includes the Java kernel and Ansatz
AOT classes, no dependency classes, and the optional Malli namespace as source.
The later seven-file [formatting correction](../measurements/parent-formatting-lineage.json)
changed whitespace only. All 177 parent source/test/build hashes match either
the original versions or the exact recorded formatting lineage.

Mathlib used the existing durable store and unchanged test fixtures. Its first
`int-arith-test` attempt stopped when sandbox restrictions denied Konserve's
normal writable file handle during a derived-cache read. An approved retry at
512 MiB heap exceeded the 1 GiB process-group RSS guard before a test summary
or fixture probe. That is a resource stop, not a test failure verdict. A final
authorized attempt with the same heap and a 1.5 GiB RSS cap required 2.5 GiB
available memory; its final preflight saw only 1,800,956 KiB and launched no
child. The other five source Mathlib namespaces and all six jar Mathlib
namespaces remain unrun. No offline/store-location override or fixture
suppression was used. No post-test Mathlib probe completed.

Existing conditional omissions remain in both successful partitions: 16 cases
need missing `test-data/init.ndjson` (split 3, induction-motive 2,
generalizing 1, rw-envlemma 3, foldl-assoc-generic 1, prelude.list 6), and one
reducer replay case needs missing `test-data/init-small.ndjson`. The prelude.list
once-fixture does not invoke its six tests. Optional Datahike tests are outside
the normal source/jar aliases and were not run. Existing auxiliary noConfusion
warnings also remain in the phase logs.

Only one validation child process group ran at a time. Guards acted only on
that group and preserved a 1 GiB system-memory floor. The resident hosted
frontend success contexts and native Store remained live. CI setup, build, formatting and unit-test jobs also passed at `69c572f`
([unit-test result](https://circleci.com/gh/replikativ/ansatz/1523)); those results
do not remove the local resource limits and fixture omissions recorded here.


## Resident/session foundation — 2026-10-18

The reviewed batch adds complete scoped proof sessions, legacy bundle inventory
and activation/packaging guards, manifest-selected store writers, and an experimental
resident frontend facade. Reviews found and fixed selected compiler/witness authority,
self-suppression during rollback, and manifest resource/consumer-path mismatches.

The fresh IR runtime suite passes 712 tests / 59,039 assertions. The rebuilt AOT JAR
passes 105 tests / 624 assertions across 18 affected namespaces; source/classes/resources
are absent from its project classpath. The JAR contains no dependency classes or optional
Malli AOT classes, and the packaged inventory/resources match source bytes. Formatting
and a deliberate corrupt-staging rejection pass. The new real-frontend probe compiles
without executing as an additional API/reader preflight.

The full parent source run at 768 MiB exhausts its heap in the existing Mathlib-backed
`ansatz.int-arith-test` fixture before a summary. A 73-namespace partition completes
662 tests / 2,505 assertions with one Omega heap failure and no errors. Both the current
Omega namespace and isolated baseline `c88f348` pass separately at 768 MiB: 19 tests /
147 assertions each. This is evidence of the combined-run resource limit, not a complete
parent-suite pass. Six large-fixture namespaces remain excluded from that partition;
missing Init fixtures and optional Datahike coverage retain their earlier limitations.
The uberjar was not built; both packaging paths use the reviewed staging guard.

Actual acceptance through the new facade remains open. The old resident REPL port was
unreachable. A fresh strict, pinned archive restore with a 2 GiB heap failed with
`OutOfMemoryError` before catalogue preparation or frontend execution (87.43 s, peak
process-group RSS 2,382,647,296 bytes). A 3 GiB attempt did not launch: available memory
was below its 4,480 MiB preflight threshold. No new ordinary/full-Init or facade acceptance
claim follows from the passing model tests. The reproducible
[prelude probe](../scripts/resident-prelude-probe.clj) checks the real three compiler
markers rather than assuming an empty kernel.

The [machine-readable record](../measurements/resident-session-foundation.json) contains
profiles, exact final code hashes, counts, exclusions and local log locations. The
coordinated 4.33 generator and strict companion coverage remain separate work; the
shipped manifest honestly inventories legacy 4.29 bytes.
