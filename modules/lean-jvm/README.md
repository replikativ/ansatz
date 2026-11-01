# Optional Lean JVM SDK

`org.replikativ/ansatz-lean-jvm` is a separate optional JDK 17 artifact. Its Java
facade loads checked compiled Lean projects and runs them on one reusable,
serialized JVM engine per Project. The runtime POM depends on Clojure 1.12.0 and
data.json 2.5.1; their normal Maven dependencies resolve transitively. It does not
require the Ansatz core/kernel artifact, Mathlib, Pattern or the older resident
World backend.

This guide describes the **unmerged next-release candidate**. Published `0.2.578`
still exposes only Nat-to-Nat, String-to-String and IO Unit convenience APIs.
The general API below requires the candidate build and is not published yet.

This is an experimental bounded profile. General named calls replace the original
three-signature restriction; `natFunction`, `stringFunction`, and `runMain` remain
conveniences. See [release review](RELEASE_REVIEW.md) for the candidate's exact
coverage and open decisions. [Historical receipts](validation.json) retain their exact scope;
they do not claim unrestricted Lean/Lake, hosted frontend or kernel integration.

## Ordinary Java dependency and artifact loading

Add the Clojars repository and this optional artifact, using the actual coordinated
published Ansatz release version for `ansatz.version` after this candidate lands.
For now, use the locally built candidate JAR to try the new API; `0.2.578` does not
contain it:

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
    LeanFunction step = project.function("Example.step");
    Object answer = step.invoke(BigInteger.ONE.shiftLeft(200), true);
    System.out.println(step.signature());
    IOResult<?> result = (IOResult<?>) project.call("Example.main");
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
Maintained helper sources and their immutable cohort rules live in
[tools/lean-producer](../../tools/lean-producer/README.md); they are separate from
the JVM runtime and the module's bundle/release configuration.

```java
var nativeCompiler = new NativeCompilerOptions(leanSysroot, producerBundle, cacheDirectory);
var options = ProjectOptions.builder(nativeCompiler)
    .sourceRoot(".")
    .rootModule("Main")
    .function("Example.step")
    .function("Example.main")
    .build();
try (Lean lean = Lean.open(); LeanProject project = lean.loadProject(projectDirectory, options)) {
    System.out.print(((IOResult<?>) project.call("Example.main")).stdout());
}
```

`NativeCompilerOptions.compatibilityProfile()` identifies
`lean-native-local-init-dag/1`. The initial profile is Linux x86-64, pinned Lean
4.33.1, one selected root module and a closed acyclic local import DAG with
installed Init. Requested entries are checked in that root's imported native
Environment, so imported local definitions can be selected there. Names use
string segments; numeric-looking segments are not parsed as numeric Names. The
string convenience form cannot express a literal dot inside one Name segment.
`rootModule` defaults to `Main`; `sourceRoot` is an explicit relative directory.

Installed Std, Lean and Mathlib imports are not resolved by this profile: a
non-Init import must belong to the captured local DAG. External package fetching,
arbitrary Lake scripts and plugins are unsupported. The admitted file header
profile is legacy private/ordinary. Unsupported paths fail explicitly; this is
not unrestricted Lake project support. Compilation can execute native
metaprograms and compile-time IO. It is a trusted-source profile, not a sandbox.
The installed sysroot is a trusted dependency with mutation checks, not full
cryptographic attestation of every library file. A separately hosted, hash-verified Linux helper bundle is available through the
producer guide. Automatic installation and platform expansion remain separate
work.

## Values, resources and lifetime

Entries have closed monomorphic signatures with up to 64 explicit value
arguments and either pure or IO results. Discovery uses the actual Lean type
before erasure, native definitional equality, original callable lookup, and
compiler layout evidence. Select one to sixteen entry names per project.
Discovery does not automatically admit every declaration in a module.

| Lean type | Java carrier | Clojure carrier |
| --- | --- | --- |
| Nat / Int | Exact integer arguments; `BigInteger` results | Exact integers |
| Bool | `Boolean` | `true` / `false` |
| String | Valid UTF-16 `String`, including NUL | String |
| Unit | `LeanUnit.INSTANCE` | `nil` |
| UInt8/16/32/64, Int8/16/32/64, USize/ISize | Range-checked exact integers; `BigInteger` results | Exact integers |
| Float / Float32 | Exact `Double` / `Float` | Double / `(float x)` |
| Char | Unicode scalar code-point integer; `Integer` result | Code-point integer, including supplementary characters |
| Prod | Two-element `java.util.List` | Two-element vector |
| Option | `Optional.empty()` / `Optional.of(value)` | `nil` / `{:some value}` |
| List | Bounded indexed `java.util.List` | Vector |
| Array | `Object[]` or bounded indexed List; immutable List result | Vector |
| ByteArray | Copied `byte[]` | Copied byte array |
| Sum | `LeanChoice.left(value)` / `.right(value)` | `{:left value}` / `{:right value}` |
| Except | Left error / right success `LeanChoice` | `{:error value}` / `{:ok value}` |

Containers nest over supported types. `none` and `some ()` stay distinct: the
latter is `Optional.of(LeanUnit.INSTANCE)` or `{:some nil}`. Results contain no
raw guest Nodes or aliases to mutable interpreter storage. Byte arrays are mutable
host copies. Finite machine integers reject out-of-range inputs rather than
truncate; arithmetic executed by Lean code retains its own wrapping semantics.
Float conversions preserve raw signed zero and nonfinite values; Lean operations
may canonicalize NaNs according to their own semantics. USize/ISize use the admitted
64-bit target profile. Char takes a code point, rather than Java's UTF-16 `char`.

IO calls return `IOResult<T>` with `value()`, `stdout()`, and `stderr()`; Clojure
returns `{:value ... :stdout ... :stderr ...}`. Calling a named IO entry does not
require it to be `main`. `runMain` requires exactly one admitted `IO Unit` entry;
use named calls if several exist. A data codec does not implement arbitrary IO:
the current task-free runtime has captured output and a limited audited intrinsic
set. Unclassified required externs are refused before startup. Declared terminal
traps and unsupported dynamic captured-stream operations can fail when reached
at runtime.

Polymorphic, implicit/dependent, proof-bearing or higher-order entry arguments,
arbitrary records/enums/recursive ADTs, constrained Fin/Vector/Subtype/Rat
adapters, callbacks, task resources, and public forks remain unsupported. The
[survey and campaign](CAMPAIGN.md) distinguish follow-up work from this boundary.
An unsupported type or capability throws; it is never replaced by a guessed value
or native execution fallback. Host argument refusal occurs before guest effects
and leaves a valid Project reusable.

Interop is bounded: 4,096-bit integer leaves, 65,536 UTF-16 units per string,
100,000 visited values/field occurrences, depth 128, aggregate integer bits
4,194,304, aggregate string units 1,048,576 and scalar/buffer bytes 1 MiB per
conversion. Signature descriptors have separate depth/node bounds. Lazy sequences
and unbounded Iterables are not materialized implicitly. These are marshalling
limits, not claims that all Lean arithmetic or program state is restricted to
those sizes.

### Clojure REPL

Add the optional SDK alongside core Ansatz if the kernel/DSL is also needed.
Core Ansatz and the SDK remain separate artifacts; using both does not merge their
declaration environments.

```clojure
(require '[ansatz.lean.jvm :as lean])
(def runtime (lean/open))
(def project
  (lean/load-project runtime project-directory
    {:compiler {:sysroot lean-sysroot :producer-bundle producer-bundle :cache compiler-cache}
     :entries ["Demo.sumArgs" "Demo.optionUnit" "Demo.main"]}))
(def sum-args (lean/function project "Demo.sumArgs"))
(sum-args 20 21 true)                         ; 42
(lean/call project "Demo.optionUnit" {:some nil}) ; {:some nil}
(lean/call project "Demo.main")             ; {:value nil :stdout "main\n" :stderr ""}
(lean/close! project)
(lean/close! runtime)
```

The executable two-file example is in
[the consumer corpus](consumer/resources/lean/general-interop-source/Main.lean).
To reload after editing source, load a new Project and rebind its function handles,
then close the old Project. Code and initialized globals belong to one Project
version; existing handles stay bound to that version until close invalidates them.
There is no implicit hot replacement or state migration.

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
initialization output, if any, is included in the first IO result.

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
inventories every runtime source/resource and pins the complete canonical Java
engine closure plus facade source files. The [implementation layout](ARCHITECTURE.md)
explains the production/research boundary and compiled-class inventory. The producer captures their exact bounded bytes,
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


CI builds this optional SDK once, then runs the canonical JAR model suite,
public application-JAR consumers, archive rejection cases, ownership/construction
checks and 41 standalone resource checks against the same compiled engine. Its launcher
requires Java and javac 17 or later and uses bounded sequential JVMs. Source
compiler helper provisioning is not part of mandatory SDK CI. The main-only SDK
deployment job receives the exact checked JAR/POM/release receipt through the
workspace and deploys verified bytes without rebuilding. GitHub release waits
for both core and optional Clojars deployment.
