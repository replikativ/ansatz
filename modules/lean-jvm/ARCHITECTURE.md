# Lean/JVM implementation layout

The production SDK owns one Java interpreter. Native source preparation, JVM
execution, maintained hosting research and historical evidence have separate homes.
The public Maven artifact split remains core Ansatz plus the optional Lean/JVM SDK.

## Production boundaries

- `src-java/ansatz/lean/jvm/`: public Java facade and value carriers.
- `src-java/ansatz/lean/jvm/internal/exec/`: canonical lambda-RC execution engine
  and package-private stateless scalar/UTF-8 helpers. The Java engine retains its
  Java 11 compilation contract; the SDK is built and tested for JDK 17.
- `src/ansatz/lean/jvm/`: Clojure API, codecs, actual runtime cohort adapters,
  initialization, artifact admission and explicit native compilation services.
- `test/`: focused Clojure contracts and active native capture fixtures.
- `test-java/`: actual Java engine ownership, resource and representation checks.
- `producer/`: supported bundle descriptors, packaging and release coordination.
- `../../tools/lean-producer/`: maintained native helper sources, including the
  supported v1 source. Moving these files does not change their admitted bytes.

The engine keeps Node/Header/Program identity, mutable execution state, pending
operations, ownership journals, suspension and fork commit points together.
Splitting those across classes is a separate ownership review, not a directory
cleanup. In particular, the adapters inspect declared fields; introducing an
engine superclass would change that contract.

`ScalarBits` and `Utf8Bytes` contain only mechanically extracted stateless
operations. Stateful intrinsic families can be extracted later with explicit
custody interfaces. Heap, IR, runtime-family and bridge packages should appear
when real implementations move into them, rather than as empty placeholders.

## Build and class inventories

`runtime-closure.edn` schema 2 lists disjoint Java engine and facade source sets.
Their union must equal the complete Java source tree. Every source is hash-pinned;
the sorted engine descriptors also have a closure digest. All source pins are
validated and their bytes captured before any Java source is staged or compiled.

The build emits `META-INF/ansatz-lean-jvm/java-classes.json`, binding each compiled
class to a captured top-level source and exact class-byte hash. Producer/consumer
checks compare it with the independently reviewed source inventory, reject unknown
or changed classes, and check runtime metadata against the interpreter and full
engine closure. No broad `internal/**` class wildcard grants packaging authority.

The JAR contains canonical runtime code and ordinary Maven dependencies. Research
loaders, native helper executables and historical captures do not enter it.

## Maintained research and retirement

The old experiment tree is consolidated under `research/lean-hosting`. Working
frontend controllers, bootstrap policies, full-Init work, graph import, forks,
tasks and code-demand contracts remain available there. Their internal evidence
and source verifiers retain explicit source-at-commit and relocation provenance.
Unpublished legacy facade/backend code is isolated as research; it is not another
public SDK or the canonical interpreter.

Closed prepared-interpreter, bulk-sparse and paged-register investigations can be
retired with their closed probe consumers. Conclusions and immutable capture
records retain their original provenance. Past acceptance hashes are never
rewritten to describe current code. See the research consolidation record for
specific retired files and the optional legacy-contract lane.

## Verification

The SDK gate builds one captured Java closure and tests the JAR, application
consumers, archive rejection, explicit ownership and resource limits. The broader
contract gate exercises the canonical engine's fork, graph, host, code-demand and
frontend foundations. The explicit source gate additionally checks the native
frontend cold/cache/edit/reload/artifact paths with a supplied supported toolchain
and bundle. No full Mathlib replay is needed for this structural consolidation.
