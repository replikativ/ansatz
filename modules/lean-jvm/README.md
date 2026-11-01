# Internal Java interpreter packaging skeleton

This optional module packages the authoritative Java interpreter and a small
Clojure adapter at `ansatz/lean/jvm/ir.clj`. It is not a public LeanProject API,
generic loader, compiler installation, complete Init image or new execution
backend. The existing provider-first `modules/lean` module is unchanged.

The runtime dependency is currently only Clojure 1.12.0. A later admitted artifact
loader can add data.json, and actual Name/store integration can add the pinned
core dependency; neither unused dependency is included by this extraction.
Build tooling is a producer alias and is absent from the emitted runtime POM.

`runtime-closure.edn` names every source/resource and the one canonical engine
source. The producer build captures its bounded, hash-checked bytes into the
owned `target/java-source/ansatz/research/ir/Interpreter.java`, then compiles only
that staging tree once with `--release 17`. The staging copy is generated build
material; no second Interpreter.java is tracked. Source neighbors are never
compiler inputs, and changes before capture fail the digest check. The build
copies the adapter source and runtime metadata into the jar. Runtime callers use `linked-basis`, which resolves the compiled
class on the application classpath. It creates no classloader, calls no javac,
and does not discover a source checkout or class-directory path.

`basis-for-class` is an internal seam for testing the adapter against an already
loaded Class. The initial wrappers intentionally resemble the research j/*
operations, but contain no IR/object/execution semantics. The Java interpreter
remains their authority. Research repl.clj and its legacy helpers remain intact;
this small extraction does not require rewriting that test suite.

The adapter creates task-free engines and optionally installs the actual engine-issued
pinned Lean build identity. It still refuses TaskRuntime and profiling policies. SourceBinding/Header metadata remains
trusted adapter input, not source authentication. Host descriptors register an
ABI, never a callback. Explicit execution may suspend or fail under the existing
engine protocol. Raw Nodes are internal trusted carriers: this module does not
claim universal engine ownership tags. Future Java handles must bind the actual
Project lease/version while exposing immutable Java values.

## Producer commands

From this module directory, a producer with the standard build tooling may run:

```sh
clojure -T:build check-package
clojure -T:build jar
```

The root built the final captured-source jar with
`clojure -J-Xmx384m -T:build jar`. Source audits passed 5 tests / 23 assertions,
and adapter checks passed 3 tests / 9 assertions in the retained JVM. The tracked
Java-only consumer then passed from an empty working directory with only the
SDK and three normal Clojure dependency jars. Archive audits accepted the actual
jar and rejected six deliberately invalid variants. The worker's archive checks
started no JVM. Portable evidence and source pins are recorded in
`validation.json`; the earlier 28cd engine jar remains a separate historical
record from the final 9a3 engine/captured-producer acceptance. A consumer
of a future published jar will not need Clojure CLI, build tooling or a source
checkout. Release preparation is separate from runtime acceptance; see the producer
release commands below.

## Checks for the root's retained JVM

The source-only audit does not require loading an engine or adapter. Load
`ansatz_lean_jvm_build_audit.clj`, then `test/build_audit_checks.clj`, and invoke
`ansatz-lean-jvm-build-audit-checks/check!` with this module directory. It checks
the actual namespace/resource inventory, exact runtime dependency set and engine
pin, plus negative namespace, resource-path and dependency cases. Capture tests
verify that an unlisted neighbor is ignored, the staged source stays fixed after
a canonical-file change, and a pre-capture mutation fails without publishing
compiler input. These source-only tests create no Java/native processes.

For adapter execution, load `src/ansatz/lean/jvm/ir.clj` and
`test/prepare_checks.clj`. Invoke `ansatz-lean-jvm-prepare-checks/check!` with the
root's already loaded Interpreter Class. These models exercise real in-memory
original-row preparation, source-bound Header mechanics, selected-body materialization
and explicit execution; they are not native evidence or source authentication.

The final acceptance also verified the built jar inventory/POM, required
`ansatz.lean.jvm.ir` from its jar resource and exercised `linked-basis` with no
research roots on the consumer classpath. These checks establish the internal
packaging boundary; they do not establish a public Project API or generic loader.

The tracked [Java-only consumer](consumer/README.md) includes the actual accepted
Java smoke source, bounded reproduction tooling, and static positive/negative
archive checks. Producer/test scripts and validation records are not jar resources.


## Coordinated optional artifact release

This artifact remains optional and separate from `org.replikativ/ansatz`. Its
version now uses the root build's `0.2.<git-count>` rule. An explicit version
coordinates a release assembled from one chosen root commit:

```sh
clojure -T:build prepare-release :version '"0.2.1234"'
```

Replace the example with the actual root release version. This producer command
builds the JAR and ordinary Maven POM, then records their exact SHA-256 digests,
version and packaged runtime cohort in `target/release.edn`. It publishes nothing.
The emitted runtime POM contains only the audited runtime dependencies; build and
deploy tooling remain confined to the build alias. The fixed JAR filename stays
`target/ansatz-lean-jvm.jar` for existing producer and consumer tooling.

After reviewing those exact files and completing the applicable runtime gates,
the release owner can explicitly publish the prepared bytes:

```sh
clojure -T:build deploy-prepared :version '"0.2.1234"'
```

This requires normal Clojars producer credentials. It verifies the receipt,
expected version, packaged POM and current bytes before deployment, and does not
rebuild. Replacing the JAR or POM after preparation invalidates the receipt.
Neither preparation nor publication constitutes generic Project API acceptance.
Current metadata continues to report `:public-project-api false` honestly.

The agreed first public API is `ansatz.lean.jvm.Lean` / `LeanProject`, both
`AutoCloseable`, with `natFunction(String)` returning
`UnaryOperator<BigInteger>`, `stringFunction(String)` returning
`UnaryOperator<String>`, and `runMain()` returning captured stdout/stderr.
Handles must bind a real Project lease/code version and checked native entry;
Nat inputs are nonnegative and String inputs must be valid UTF-16. One Project
serializes calls on one persistent engine and invalidates all handles on close
or branch failure. No raw guest Nodes, callbacks or fork enter this surface.
These classes are a contract for subsequent work, not included implementations.

Precompiled resource/InputStream artifact loading must work using ordinary
Maven/Gradle resolution alone, without a source checkout, Clojure CLI, Python,
runtime javac or native Lean installation. Trusted source compilation is a
separate service using an explicitly configured pinned toolchain and independent
platform helper. Helper distribution is unresolved; this release preparation
adds no helper binaries or platform-support claim. Core/kernel stores, hosted
frontend state and Mathlib remain separately selected services/cohorts.
