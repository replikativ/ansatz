# Ansatz Lean/JVM SDK

`org.replikativ/ansatz-lean-jvm` runs compiled Lean functions inside a Java or
Clojure application. The official native Lean frontend prepares a project's
compiler IR during your build; the SDK loads that prepared artifact and
interprets the IR on the JVM. Deployed applications need only this JAR and its
ordinary Maven dependencies: no Lean installation, native helpers or javac.

The SDK is an experimental, bounded profile. It targets JDK 17+, official Lean
**4.33.1** and Linux x86-64 for preparation. The [compatibility ledger](COMPATIBILITY.md)
lists what is supported and what is refused. It does not require the core Ansatz
kernel artifact or a Mathlib store; using both in one application does not merge
their declaration environments.

**Guides:** [preparation](PREPARATION.md) · [values](VALUE_EXAMPLES.md) ·
[host bindings](FFI.md) · [stdio](STDIO.md) · [filesystem](FILESYSTEM.md) ·
[Lake workspaces](LAKE.md) · [producer bundles](producer/README.md) ·
[examples](examples/README.md) · [architecture](ARCHITECTURE.md) ·
[maintainers](#maintainers)

## Install

```xml
<repositories>
  <repository><id>clojars</id><url>https://repo.clojars.org/</url></repository>
</repositories>
<dependencies>
  <dependency>
    <groupId>org.replikativ</groupId>
    <artifactId>ansatz-lean-jvm</artifactId>
    <version>${ansatz.version}</version>
  </dependency>
</dependencies>
```

```clojure
{:deps {org.replikativ/ansatz-lean-jvm {:mvn/version "..."}}}
```

The runtime POM depends on Clojure 1.12.0 and data.json 2.5.1. Releases share the
`0.2.<n>` version line of core Ansatz; the general call API exists from 0.2.580.

## Prepare an artifact at build time

Preparation needs an installed official Lean 4.33.1 sysroot, Linux `prlimit`, a
writable cache, and the published [native producer bundle](producer/README.md)
(use the current v4 bundle). It compiles *trusted* sources: the native frontend can
run metaprograms and compile-time IO, so preparation is not a sandbox.

```sh
java -cp "$SDK_CLASSPATH" ansatz.lean.jvm.LeanPreparation \
  --source ./lean-src --sysroot "$LEAN_SYSROOT" \
  --producer-bundle "$PRODUCER_BUNDLE" --cache "$COMPILER_CACHE" \
  --root-module Main --entry Example.step --entry Example.main \
  --output ./my-project.zip
```

The command refuses an existing output and prints JSON with `manifest-sha256` and
`archive-sha256`. Keep the manifest digest in your application's trusted
configuration. The [preparation guide](PREPARATION.md) covers the Java/Clojure
preparation API, and [LAKE.md](LAKE.md) the `--source-mode built-lake` path for an
already built Lake workspace.

Source profile: one root module and an acyclic graph of local modules plus Init;
exact installed modules can be added with `ProjectOptions.Builder.installedImport`
(`:installed-imports` in Clojure); a project's non-Init module closure is limited to
128 modules. Entries are explicitly selected top-level functions with closed
monomorphic signatures, 0–64 explicit arguments, pure or `IO` results; one artifact
selects up to 1,024 entries. Discovery uses the actual Lean types before erasure,
so arguments are not guessed from Java values.

**An artifact contains the Lean source files and compiled `.olean` modules** of
its local closure alongside the IR, as custody evidence for the manifest. Treat a
prepared artifact like the source itself when the code is proprietary.

## Load and call

```java
try (Lean lean = Lean.open();
     LeanProject project = lean.loadArtifact(
         MyApp.class.getClassLoader(), "lean/my-project.zip", expectedManifestSHA256)) {
    LeanFunction step = project.function("Example.step");
    Object answer = step.invoke(BigInteger.ONE.shiftLeft(200), true);
    IOResult<?> result = (IOResult<?>) project.call("Example.main");
    System.out.print(result.stdout());
}
```

`loadArtifact` also takes an `InputStream` (the caller keeps ownership of it).
Loading checks the manifest digest you supply, then every archive entry's size and
SHA-256 against that manifest, before parsing anything else; it then validates
format, target, entry evidence, runtime ABIs and the admitted capability profile.
A prepared artifact is native frontend evidence, not a kernel proof certificate:
the compiler, this interpreter and the host integration are part of the trusted
execution path.

From Clojure:

```clojure
(require '[ansatz.lean.jvm :as lean] '[clojure.java.io :as io])
(with-open [runtime (lean/open)
            input   (io/input-stream "my-project.zip")
            project (lean/load-artifact runtime input expected-manifest-sha256)]
  (let [step (lean/function project "Example.step")]
    [(step 42 true)
     (lean/call project "Example.main")]))   ; IO => {:value .. :stdout .. :stderr ..}
```

`Lean.loadProject(sourceRoot, ProjectOptions)` (Clojure `lean/load-project`)
prepares and loads trusted sources in one step during development; it needs the
same native tools as preparation.

## Values

| Lean type | Java | Clojure |
| --- | --- | --- |
| Nat / Int | exact integer arguments; `BigInteger` results | exact integers |
| Bool, String, Unit | `Boolean`, `String`, `LeanUnit.INSTANCE` | boolean, string, `nil` |
| UInt8…64, Int8…64, USize/ISize | range-checked integers; `BigInteger` results | exact integers |
| Float / Float32 | `Double` / `Float` | double / float |
| Char | Unicode code point (`Integer`) | code point (BMP results as characters in v3) |
| Prod, List, Array | immutable `java.util.List` (arrays also accept `Object[]`) | vectors |
| Option | `Optional` | `nil` / `{:some v}` |
| ByteArray | `byte[]` copy (v3: immutable `LeanBytes`) | byte array |
| Sum / Except | `LeanChoice` left/right | `{:left v}`/`{:right v}`, `{:error v}`/`{:ok v}` |
| Enums, records, recursive datatypes (v3 producer) | immutable `LeanData` | tagged map views |

Machine integers reject out-of-range inputs rather than truncate; arithmetic inside
Lean keeps Lean's wrapping semantics. Conversions are bounded: 4,096-bit integer
leaves, 65,536 UTF-16 units per string, 100,000 visited values, depth 128 (1,024 for
v3 typed values), 1 MiB of scalar/buffer bytes per conversion. Detached v3 values
can be materialized with `LeanType.materialize` / `lean/materialize` and reused in
a compatible Project. Details and nested examples: [VALUE_EXAMPLES.md](VALUE_EXAMPLES.md).

`IO` entries return `IOResult` with `value()`, `stdout()` and `stderr()`.
`runMain()` runs the single admitted `IO Unit` entry. Per-call stdin and output
limits are set with `InvocationOptions` ([STDIO.md](STDIO.md)). Lean code can call
registered Java/Clojure functions through [typed host bindings](FFI.md), and an
explicit [filesystem context](FILESYSTEM.md) can be granted with
`Lean.open(HostServices)`; the default scope grants no filesystem access.

## Running in a service

**One Project is one version of code and initialized globals.** Open it once and
reuse its `LeanFunction` handles; calls are serialized per Project, so use several
Projects for parallelism. Loads run concurrently. To deploy new code, load a new
Project, rebind handles, then close the old one; there is no hot replacement or
state migration. `close()` waits for an in-flight call and then invalidates handles.

**Budgets.** Every call has a cooperative budget, by default two million
interpreter instructions and five seconds:

```java
var options = InvocationOptions.empty().withBudget(500_000_000L, Duration.ofSeconds(30));
Object value = step.invokeWith(options, input);       // or project.callWith(name, options, args...)
var services = HostServices.builder().startupBudget(50_000_000L, Duration.ofSeconds(30)).build();
Lean lean = Lean.open(services);                       // budget for module initialization
```

In Clojure: `(lean/function project name {:instruction-budget 500000000 :time-budget-ms 30000})`.
Budgets are checked at bounded intervals; they are not JVM heap caps or
preemption, and a long atomic JDK call can hold its thread until it returns.

**Failures.** Arguments are validated before execution; a refused argument or
input quota leaves the Project usable, and so does an `IO` entry that *returns* an
error (`LeanException` code `GuestIOError`, with `userError` messages in
`details()`). A failure *during* execution, such as an exhausted budget
(`ResourceLimit`), interruption (`Cancelled`) or an unsupported operation reached at
runtime, leaves guest state unknown and retires the engine: later calls fail with
`ProjectFailed`. Recover without reloading the artifact:

```java
try {
    result = step.invoke(input);
} catch (LeanException e) {
    if (project.isFailed()) project.restart();   // fresh engine from the verified artifact
    throw e;
}
```

`restart()` keeps function handles valid and reruns module initializers, so
globals and `IO.Ref` state start over. External effects of the failed call, such as
file writes or host callbacks, are not undone. Clojure: `lean/failed?`, `lean/restart!`.

**Panics** follow native Lean: `panic!` and out-of-bounds `xs[i]!` write their
message to stderr and continue with the type's default value. For `IO` entries the
message is in `IOResult.stderr()`; for pure entries it goes to the process
`System.err`; during module initialization it is suppressed, as in compiled Lean
executables. `InvocationOptions.withFailOnPanic(true)` (`:fail-on-panic? true`)
turns a reached panic into a `LeanPanic` failure instead, like `LEAN_ABORT_ON_PANIC`.

`LeanException` carries bounded value-only data (`code()`, `category()`,
`getMessage()`, `details()`), never guest objects. Fatal JVM errors and `Error`s
thrown by host bindings propagate unchanged.

**Performance.** The engine interprets Lean's compiler IR; the JVM JIT optimizes
the interpreter, but there is no Lean-specific JIT yet. As a rough guide, a
million-iteration `Nat` loop runs in about half a second after warm-up. The first
`Lean.open()` in a JVM loads the SDK's Clojure layer.

## Maintainers

From this module directory:

```sh
clojure -X:audit                                  # source inventory and Java source pins
clojure -X:repin                                  # recompute pins after editing Java sources
clojure -T:build prepare-release :version '"0.2.1234"'
../../bin/run-lean-jvm-checks                     # full JVM-only gate against the built JAR
../../bin/run-test-contracts                      # engine contracts (test-engine/)
```

`runtime-closure.edn` inventories every runtime source and resource and pins the
Java engine and facade sources by SHA-256; the build compiles exactly those bytes
with `--release 17`. `target/release.edn` records the JAR/POM digests;
`deploy-prepared` deploys those reviewed bytes without rebuilding. CI builds the
SDK once, runs the JAR model suite, the [application-JAR consumers](consumer/README.md)
and resource checks against it, then a native job (`bin/lean-jvm-native-ci`)
prepares the Lake corpus with the pinned toolchain and producer bundle.

Maintainer records live in [dev/](dev/): the [release checklist](dev/RELEASE_CHECKLIST.md),
the [datatype interop design](dev/DATATYPE_INTEROP_PLAN.md), historical
[validation receipts](validation.json) and [source migration records](producer/migration.json).
Native producer sources are in [tools/lean-producer](../../tools/lean-producer/README.md).
