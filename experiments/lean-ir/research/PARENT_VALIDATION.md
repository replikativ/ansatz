# Parent Ansatz validation after hosted source imports

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
