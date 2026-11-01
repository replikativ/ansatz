# Optional Lean JVM SDK

`org.replikativ/ansatz-lean-jvm` is a separate optional JDK 17 artifact. Its Java
facade loads checked compiled Lean projects and runs them on one persistent,
serialized JVM engine per Project. The runtime POM depends on Clojure 1.12.0 and
data.json 2.5.1; their normal Maven dependencies resolve transitively. It does not
require the Ansatz core/kernel artifact, Mathlib, Pattern or the older resident
World backend.

The current assembly is a source-reviewed release candidate. Public API
acceptance metadata remains false until the rebuilt canonical SDK, native source
path and application-JAR consumer pass their root-owned runtime gates. Historical
research receipts do not establish acceptance of this new source closure.

## Ordinary Java dependency and artifact loading

Add the Clojars repository and this optional artifact, using the actual coordinated
published Ansatz release version for `ansatz.version`:

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

A precompiled artifact resource belongs in the application JAR. Its independently
expected manifest digest comes from the application's trusted build descriptor;
a digest supplied by the same untrusted input is not that trust boundary.

```java
try (Lean lean = Lean.open();
     LeanProject project = lean.loadArtifact(
         MyApplication.class.getClassLoader(), "lean/my-project.zip", expectedManifestSHA256)) {
    var step = project.natFunction("Example.step");
    BigInteger answer = step.apply(BigInteger.ONE.shiftLeft(200));
    var echo = project.stringFunction("Example.echo");
    String text = echo.apply("λ\0😀");
    MainResult result = project.runMain();
    System.out.print(result.stdout());
}
```

The classes are in `ansatz.lean.jvm`. The InputStream overload leaves the supplied
stream owned by its caller; the classloader overload closes the resource stream
it opens. Artifact loading validates bounded bytes, format, target, native checked
entry evidence, exact runtime ABIs and the admitted capability profile. It does
not discover a toolchain, launch Lean, fetch a store, load a source compiler,
invoke javac or require Python, Clojure CLI or a source checkout. A compiled
artifact is native frontend evidence, not a Java kernel proof certificate.

## Explicit trusted source compilation

Source compilation additionally needs a pinned installed official toolchain and
the separate [native producer bundle](producer/README.md). The library invokes
its helpers itself; callers do not perform a manual export step.

```java
var nativeCompiler = new NativeCompilerOptions(leanSysroot, producerBundle, cacheDirectory);
var options = ProjectOptions.builder(nativeCompiler)
    .sourceRoot(".")
    .rootModule("Main")
    .main("main")
    .natFunction("answer")
    .stringFunction("echo")
    .build();
try (Lean lean = Lean.open(); LeanProject project = lean.loadProject(projectDirectory, options)) {
    System.out.print(project.runMain().stdout());
}
```

`NativeCompilerOptions.compatibilityProfile()` identifies
`lean-native-local-init-dag/1`. The initial profile is Linux x86-64, pinned Lean
4.33.1, one selected root module and a closed acyclic local import DAG with
installed Init. Requested entries are checked in that root's imported native
Environment, so imported local definitions can be selected there. Names use
string segments; numeric-looking segments are not parsed as numeric Names.
`rootModule` defaults to `Main`; `sourceRoot` is an explicit relative directory.

Source imports of Std, Lean and Mathlib, external package fetching, arbitrary Lake
scripts and plugins are unsupported. Unsupported paths fail explicitly; this is
not unrestricted Lake project support. Compilation can execute native
metaprograms and compile-time IO. It is a trusted-source profile, not a sandbox.
The installed sysroot is a trusted dependency with mutation checks, not full
cryptographic attestation of every library file. Native helper hosting,
automatic installation and platform expansion remain separate work.

## Values, resources and lifetime

The initial entries are closed monomorphic Nat-to-Nat, String-to-String and IO
Unit. Lookup requests a genuinely native-checked signature. It never grants
caller-supplied type authority. Nat uses exact nonnegative `BigInteger`, with a
4096-bit public codec bound; String preserves Unicode and NUL, rejects malformed
UTF-16 and has a 65536-unit public codec bound. No raw guest Nodes, arbitrary Java
objects, task callbacks, fork, polymorphic or dependent entry API is exposed.

One Project initializes its module world once. Calls reuse its code and globals,
including initialized random state, and are serialized across threads. One Lean
scope lazily owns a shared JDK DRBG capability using its actually selected JDK
provider. It neither clones nor reseeds that service per call. Project close
never claims to close undocumented JDK provider resources.

Calls use a cooperative two-million-instruction/five-second budget with bounded
quanta, guarded Nat operations, and the engine's allocation/output profile.
These are not hard JVM heap caps, preemption or wall-clock guarantees; an atomic
JDK/library call can occupy its thread until it returns. Host interruption stops
at a supported boundary. A failed branch becomes unusable and is never replayed
or silently executed natively. `runMain` returns per-call captured stdout/stderr;
initialization output, if any, is included in the first main result.

`LeanProject.close()` invalidates retained handles and retires known owners.
Supported stopped failures use the issuer's independently checked task-free
pure-heap abandonment path: private graph references are dropped for JVM GC,
without claiming guest DEC, finalizers, rollback or that GC ran. Close is
idempotent; Lean close attempts all its children. Ordinary `LeanException`
diagnostics are bounded value-only code/category/message data, without raw
causes or owner packets. Actual fatal host `Error` values retain their identity,
class and standard JVM Throwable semantics, including any cause they own.

## Producer build and acceptance

From this module directory:

```sh
clojure -T:build check-package
clojure -T:build prepare-release :version '"0.2.1234"'
```

Replace the example with the chosen root release version. The optional artifact
uses the same `0.2.<git-count>` rule as the root release. `runtime-closure.edn`
inventories every runtime source/resource and pins the one canonical interpreter
plus Java facade source files. The producer captures their exact bounded bytes,
compiles that staging tree with `--release 17`, and emits an ordinary Maven POM.
Consumers never compile Java sources at runtime.

`target/release.edn` records exact JAR/POM digests, version and runtime cohort.
After reviewing those bytes and completing required runtime gates, the release
owner can explicitly run `deploy-prepared` with the same version. It verifies
unchanged reviewed bytes and does not rebuild. Preparation publishes nothing.
Build/deploy tools are confined to the producer alias.

The [consumer checks](consumer/README.md), source inventory/capture tests,
strict JSON checks, lifecycle/profile checks and fresh canonical source/cache
acceptance are independent gates. [Source migration records](producer/migration.json)
identify the frozen originals, mechanical namespace changes and reviewed SDK
changes. Maintain canonical `ansatz.lean.jvm.*` sources going forward; research
snapshots preserve historical evidence.
