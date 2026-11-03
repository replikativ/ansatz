# Canonical engine contracts

`bin/run-test-contracts` compiles the maintained Java engine into an isolated test
JAR and runs its contracts with a 384 MiB heap. Build core Ansatz first, as in CI.
The engine tests do not load the archived World interpreter, provider facade,
Pattern compiler, or historical frontend controllers.

The suite covers recursive and explicit execution, reference counts and owner
transfers, continuations, task boundaries, eager forks, code demand, source/Header
identity, initialization, native Expr workers, graph imports, and independently
checked kernel projection. `checks/` contains the engine contracts; `support/`
contains their fixture builders and reflection helpers. `kernel-support/` contains
carrier-parametric checking code and a small test carrier, with its contracts in
`kernel-contracts/`. Source/artifact authority contracts also run in the SDK gate;
see the [source authority migration](source-contracts/README.md) for their current scope.

`corpus.zip` contains immutable fixture data, provenance, licenses, source oracle
producers, and their captured observations. It contains no archived interpreter
implementation. `fixture-index.json` inventories every entry with its byte count,
SHA-256, and origin. The materializer checks the exact archive/index inventory and
each digest before writing a fresh isolated working directory. Original fixture
paths and bytes remain intact so embedded producer receipts retain their meaning.
Tests write temporary working files inside that directory; the runner removes it
afterward.

The four Lean oracle captures retain their original producer sources and Lean
revision. The RBMap and 81 constant-declaration comparisons use a separate capture
from the archived Clojure World interpreter at commit `4ace73f0`. That capture
preserves exact values and allocation/store counts. Its record identifies its
inputs and World source inventory; `oracles/capture-world-oracles.clj` can reproduce
it with the archived source classpath. It is explicitly a World oracle, rather
than a native Lean observation, and is never regenerated from the Java engine
under test.

Five private report-protocol suites were retired with their corresponding private
entry points: machinery reports, mixed MVar reports, direct-pass reports, delayed
command reports, and delayed-report controls. Their fixture builders were reduced
to the functions used by maintained native tests. Full Expr semantic, control,
and adversarial tests enter the original configured native function through
generic invocation. Native lift/substitution, raw/boxed/FAP/PAP/AP entry, code-demand,
fork, and ownership tests remain. The old total test count is not a coverage
invariant; `coverage.json` records the groups and explicit retirements.

For an existing Clojure process, load `check-runner.clj` with
`*command-line-args*` bound to `[]`, then call `engine-contracts/run!` with an
absolute compiled engine directory or JAR. Include `support`, `kernel-support`,
`kernel-contracts`, core Ansatz, and the compiled `TypedLongMemo` utility on that
process's classpath. Run from a freshly materialized corpus directory.


The canonical engine contract runner requires JDK 17, matching the optional SDK.
It compiles the exact interpreter/helper/provider sources with `--release 17`.
The kernel memo fixture remains compiled with `--release 11`; this does not add
an optional SDK dependency to core Ansatz startup or its kernel artifact.


`test-java/FrozenStorageChecks.java` exercises the private storage foundation with
fixed internal plans: bounded typed freeze, persistent pure-data storage,
publication, certified input reuse, copy-on-write updates, forks, and release.
It is included in `bin/run-lean-jvm-checks`; it does not issue native layout
or public nominal admission authority. First freeze accounts actual physical
storage once; cached frontiers use constant-time conservative bounds, so distinct
overlapping frontiers can exceed a budget even when their exact union would fit.
The public legacy decoders still materialize their existing carriers.

The original fixed record test plan proves physical pure storage and sequential
raw-byte lane coverage only. `TypedStorageChecks.java` separately exercises the
private normalized semantic compiler, finite references, stable compatibility
keys, constructor alternatives, Bool/Char and scalar domains, detached canonical
construction, raw-field child access, and root-only boxed argument tokens. The
embedded native004 observations supply internal layout facts; they are not
admitted evidence. The separate [native captures](../test/fixtures/nominal-entry-v3/README.md)
and [nominal application consumer](../consumer/NominalSmoke.java) exercise actual
v3 product/entry admission and independent constructors/readers. The private
`payloadCost` bound counts scalar/buffer bytes separately from `stringUnits`,
which counts logical String UTF-16 units. Every String occurrence counts,
including repeated shared leaves and repeated uses of the same certified input,
as in ordinary legacy recipes. Neither bound measures retained heap. Shared-input
construction composes certified child depth with fresh records and Arrays before
guest allocation, with a maximum root depth of 1,024. A leaf, byte buffer, or
scalar box has depth one; a fresh record or Array adds one to its deepest field.
Certified depth includes any erased wrapper in its private plan. Ordinary legacy
construction without certified inputs keeps its existing depth behavior. These
are private-foundation checks, not public immutable-value guarantees.


The typed core rejects delegating unmodifiable input wrappers, snapshots only
exact trusted data carriers, and bounds validation work before scanning strings.
The snapshot scan-work ceiling is 1 MiB of UTF-16 units per schema document and
2 MiB per construction tape including its metadata. This is separate from the
1 MiB logical String aggregate limit, which counts every logical occurrence.
Argument preparation rechecks cached logical and physical proof bounds before
allocating any shallow scalar box. A private detached-construction allocation
counter supports refusal tests; ordinary interpreter execution is not instrumented.

Frozen sharing adds one private volatile stamp reference to each Node. The exact
field-inventory contract records this common-node cost and prevents unrelated
per-Project or pointer-allocator state from accumulating there. Actual object
size depends on JVM reference compression and alignment; no fixed byte-size
claim is made by that reflection check.
