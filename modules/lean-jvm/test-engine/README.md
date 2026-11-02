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
see the repository's contract migration record for their current scope.

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
