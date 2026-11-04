# Java application-JAR consumer

`ProjectSmoke.java` uses the actual public `Lean` / `LeanProject` facade with an
original Ansatz interop artifact packaged in its application JAR. Its source is
in `resources/lean/interop.zip`; the independent expected manifest hash is fixed
in the consumer and recorded in `resources/lean/interop.json`.

The fixture checks Nat at 0, 42, Long.MAX_VALUE, 2^64 and 2^200, exact Unicode/NUL,
checked-signature rejection, negative/malformed arguments without poisoning a
live Project, idle thread handoff, repeated captured IO Unit output and retained
handle invalidation after idempotent close. It also verifies that the source
compiler and legacy prototype namespaces never loaded. Its original source is
`Main` importing local `MathCore` and `Text.Core`, with `answer n = twice n + 1`,
`echo s = "Hello, " ++ s` and a main greeting. Init output follows the pinned Lean
Apache-2.0 cohort. The additional FP Lean sort fixture has separate attribution
in [fp-lean-sort.NOTICE](resources/lean/fp-lean-sort.NOTICE).

Resolve the SDK plus Clojure 1.12.0, spec.alpha 0.5.238, core.specs.alpha 0.4.74 and
data.json 2.5.1 through ordinary Maven dependency resolution. Then, from the module
producer directory:

```sh
python3 consumer/project_check.py --sdk-jar target/ansatz-lean-jvm.jar --dependency-jar "$CLOJURE_JAR" --dependency-jar "$SPEC_JAR" --dependency-jar "$CORE_SPECS_JAR" --dependency-jar "$JSON_JAR" --output target/public-consumer
```

This producer/test script audits the actual SDK archive, compiles the Java test
with release 17, builds a separate application JAR containing its classes and
resources, then executes it from an empty working directory. The runtime
classpath is that application JAR and the five normal dependency JARs. It
contains no source directory, Python, Clojure CLI, Lean installation or runtime
javac. The runtime Java heap is 384 MiB. Python and javac are producer/test tools.

[sdk_audit.py](sdk_audit.py) audits the actual SDK archive against the reviewed
source inventory, compiled-class inventory, runtime resources and Maven dependencies.
Static rejection checks mutate real archive bytes, including self-inventoried
helpers, source relabeling, changed classes and dependency drift:

```sh
python3 consumer/audit_checks.py --sdk-jar target/ansatz-lean-jvm.jar
```

Lower-level start/advance/result/reuse checks run in the packaged SDK
[preparation checks](../test/prepare_checks.clj). Published historical observations remain in
[validation.json](../validation.json) and [consumer receipts](receipts/).
Current candidate results belong in CI/review artifacts; see
[release checks](../dev/RELEASE_CHECKLIST.md).

## General application-value consumers

`GeneralInteropSmoke.java` loads the original two-file
[common corpus](resources/lean/general-interop-source/Main.lean) from
`resources/lean/general-interop.zip`. It checks arity, all five core value types,
nested products/options/lists, Some Unit versus None, exact named IO dispatch,
argument refusal without losing a healthy Project, Clojure round-trips and close.
Its independent trusted descriptor is [general-interop.json](resources/lean/general-interop.json).

`ScalarInteropSmoke.java` loads the original
[scalar corpus](resources/lean/scalar-interop-source/Main.lean) from
`resources/lean/scalar-interop.zip`. It checks both float widths, wrapping machine
arithmetic, all machine integer widths, Unicode scalar chars, array/byte snapshots
and updates, Sum/Except, nested IO results and explicit range/type rejection.
Its descriptor is [scalar-interop.json](resources/lean/scalar-interop.json).
[Oracle.lean](resources/lean/scalar-interop-source/Oracle.lean) checks representative
results using official native Lean; it is producer test material.

Pass `--main-class GeneralInteropSmoke` or `--main-class ScalarInteropSmoke` to
`project_check.py` with the same five-JAR closure and a separate output directory.
Each resulting application JAR runs without a source compiler, Lean installation
or native helper, and asserts that the source compiler namespace never loaded.
The fixtures are native frontend evidence, not Java-kernel-checked declarations.

`SortSmoke.java` uses the [unchanged proof-backed tutorial](../examples/fp-lean-sort/README.md)
through three explicit IO adapters. Its independently fixed manifest hash and
[descriptor](resources/lean/fp-lean-sort.json) identify the prepared artifact. It
checks repeated calls, original-array/host-data preservation, supplementary
Unicode ordering, captured sharing diagnostics, Clojure calls and handle cleanup.
Pass `--main-class SortSmoke` to the same application-JAR launcher. This consumer
also runs from an empty directory without source/native tools on the classpath.

For the explicit native source gate, use the built SDK JAR and ordinary runtime
JARs on the classpath, run from this module, and provide a new output directory:

```sh
java -Xmx512m -Xss8m -cp "$CLASSPATH" clojure.main test/source_acceptance.clj \
  "$LEAN_SYSROOT" "$PRODUCER_BUNDLE" "$NEW_OUTPUT_DIRECTORY"
```

This gate observes actual compiler cache results and issued build receipts. It
checks cold/cache/edit/reload/artifact paths, both corpora, warnings and errors,
unsupported capabilities and higher-order entry rejection. It changes only its
new owned output directory. The published v2 helper bundle is required; no download
or installation is performed. The mandatory JVM-only CI gate needs no toolchain.

## Finite stdin and byte output consumer

`StdIOSmoke.java` loads the native-prepared [stdio fixture](resources/lean/stdio-source/Main.lean)
from `resources/lean/stdio.zip`, using the independent manifest hash in
[stdio.json](resources/lean/stdio.json). It exercises public Java invocation
options and Clojure `call-with-options`: byte snapshots, fresh input on repeated
calls, EOF, newline/Unicode/NUL handling, captured stderr, split UTF-8 writes and
unchanged invalid output bytes. Mutating returned byte arrays does not change
stored captures. Invalid text options are refused before guest execution.

Run the existing launcher with `--main-class StdIOSmoke` and a fresh output
directory. The consumer uses the SDK and its ordinary Maven dependencies;
source preparation and native reference execution are producer-side acceptance
checks, not part of its runtime path.

## Monad runners and bounded IO errors

`MonadsSmoke.java` loads the native-prepared [monad artifact](resources/lean/monad-conformance.zip)
with the pinned manifest in [monad-conformance.json](resources/lean/monad-conformance.json).
Its [closed Lean adapters](../examples/monad-conformance/Main.lean) exercise
ReaderT/State/Except ordering, ST references, all four body/cleanup outcomes for
EST and ExceptT finally, BaseIO/EIO runners, StateRefT, and IO catch/finally.
Retained handles reuse one initialized global counter across calls. A Clojure
function call checks the same public value conversion without a compiler namespace.

Fresh projects exercise actual uncaught `IO.userError` messages, including Unicode,
NUL, empty text, the 2048-unit boundary and surrogate-safe truncation. The consumer
checks immutable value-only exception details, generic treatment of another
IO.Error variant, that a returned IO error leaves the Project ready, successful
close, and isolation from the healthy retained project. The IO Unit error entry uses this artifact's AUTO
v2 evidence; it does not verify the legacy source codec path.

Run the existing launcher with `--main-class MonadsSmoke` and a fresh output
directory. This is a JVM-only application-JAR check; independent native oracle
comparison remains a producer-side check in `test/monad_acceptance.clj`.

## Explicit installed-library imports

`PersistentMapSmoke.java` loads the native-prepared
[persistent-map artifact](resources/lean/persistent-map.zip), using the independent
manifest in [persistent-map.json](resources/lean/persistent-map.json).
The [unchanged upstream regression](../examples/persistent-map/README.md) exercises
Lean.Data.PersistentHashMap insertion, update, deletion, collisions and 200-key
map equivalence. Repeated Java handles and a Clojure call must produce `OK\n`.

Run the existing launcher with `--main-class PersistentMapSmoke` and a fresh
output directory. Its empty working directory and application JAR contain no
source checkout or native toolchain dependency. Compiler transport stays
unloaded. Product provenance travels in the authenticated artifact; artifact
loading does not inspect the consumer's sysroot.


## Two-file filesystem tutorial

`FelineSmoke.java` loads the unchanged tutorial's native-prepared
[feline artifact](resources/lean/feline.zip), pinned by the independent
[feline descriptor](resources/lean/feline.json). It explicitly supplies
`HostServices` with a trusted read-only root, then exercises Java/Clojure calls,
finite stdin, file ordering and raw binary output. Independent Projects cover
missing permissions, output/read limits and directory-policy refusal, with a
healthy peer retained across failures. No native compiler namespace is loaded.

Run the launcher with `--main-class FelineSmoke` and a fresh output directory.
The [filesystem contract](../FILESYSTEM.md) distinguishes supported regular-file
semantics from explicit policy refusals. Native references and source/cache
preparation remain separate [producer-side gates](../test/filesystem_acceptance.clj).

`WriterSmoke.java` is the authored writable counterpart to unchanged Feline. Run
`project_check.py --main-class WriterSmoke` with the usual SDK/dependency options
and a fresh output directory. It takes no application arguments and loads the
validated `lean/writer.zip` artifact with the manifest pinned in `writer.json`.
It opts in with `FileAccess.readWrite`, calls the application through both public
Java and Clojure APIs, and checks final text/UTF-8/NUL/binary/log bytes. A read-only
Project refuses the first write mode before output creation. Fixture files are
removed only after all Project/runtime scopes close; the empty working directory
is restored.

The artifact was produced by the ordinary source/cache/artifact campaign and
compared with the same authored application's independent native execution,
including all five final files, source hashes, stdout, stderr and exit status.
It is not a third-party application. The native-free
[writing checks](../test/filesystem_writing_checks.clj) additionally cover write
quota side effects, resource retirement, healthy peers and interruption after a
real physical write. Initializer IO remains refused by the existing engine
models; these checks do not claim a new initializer-write execution campaign.


## Automatic datatype application

`NominalSmoke.java` loads `resources/lean/datatypes.zip`, prepared from the three
ordinary modules in [the expression application](../examples/datatypes/README.md).
Its independent expected manifest hash and native output observation are retained
in [datatypes.json](resources/lean/datatypes.json). This is an authored application,
not an upstream tutorial or a handwritten schema fixture.

Run `project_check.py --main-class NominalSmoke` with the same dependency arguments
as above. The consumer covers native-derived constructor/field metadata, Java
host construction, Clojure tagged views and materialization, IO custom results,
bounded guest error details, aggregate refusal without poisoning the Project,
shared immutable bytes, detached descriptors after close, and concurrent reuse
in two Projects. It checks that native compiler namespaces never load. The
canonical SDK runner includes this consumer alongside the existing corpus.

`LakeWorkspaceSmoke.java` consumes the authored two-package
[Lake fixture](../test/fixtures/lake-workspace/README.md). Its artifact exercises
dependency initialization, nominal values and dependency host bindings from Java
and Clojure, then checks that the Lake source compiler was never loaded. The
[fixture provenance](../test/fixtures/lake-workspace/provenance.json) records the
source, native output and archive identities.

`ServiceSemanticsSmoke.java` consumes `resources/lean/service-semantics.zip`,
prepared from [Svc.lean](resources/lean/service-semantics-source/Svc.lean) with
Lean 4.33.1 and the v4 producer. It checks per-call budgets and their bounds,
`ProjectFailed` after an execution failure and in-place `restart()` with retained
handles, native panic semantics (stderr message, default value; `System.err` for
pure entries) and the fail-on-panic policy, a returned IO error leaving the Project
ready, and a startup budget refusal.
