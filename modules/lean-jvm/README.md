# Optional Lean JVM SDK

`org.replikativ/ansatz-lean-jvm` is a separate optional JDK 17 artifact. Its Java
facade loads checked compiled Lean projects and runs them on one reusable,
serialized JVM engine per Project. The runtime POM depends on Clojure 1.12.0 and
data.json 2.5.1; their normal Maven dependencies resolve transitively. It does not
require the Ansatz core/kernel artifact, Mathlib, Pattern or the older resident
World backend.

This guide describes the general interop and preparation APIs in the current
source tree. These APIs are available starting with SDK `0.2.580`. Earlier
releases expose only Nat-to-Nat, String-to-String and IO Unit convenience APIs.
The new v3 datatype boundary described below is implemented in this source tree;
its reviewed producer archive has not yet been published. This is not a claim
that a released SDK or the published v2 bundle exposes those types.
The opt-in [regular-file filesystem context](FILESYSTEM.md) and v3 datatype
support below are later additions; this paragraph does not put them in 0.2.580.

This is an experimental bounded profile. General named calls replace the original
three-signature restriction; `natFunction`, `stringFunction`, and `runMain` remain
conveniences. See [release checks](RELEASE_CHECKLIST.md) for acceptance and
publication order. [Historical receipts](validation.json) retain their exact scope;
they do not claim unrestricted Lean/Lake, hosted frontend or kernel integration.

The unchanged two-file [Feline tutorial](examples/fp-lean-feline/README.md) is the
candidate filesystem example. `Lean.open(HostServices)` supplies an explicitly configured
root for either source or artifact loading; default `Lean.open()` grants no
filesystem service. [The service contract](FILESYSTEM.md) covers limits,
ownership, retirement and explicit unsupported domains.

## Ordinary Java dependency and artifact loading

Add the Clojars repository and this optional artifact. Set `ansatz.version` to
the coordinated published release you intend to use, at least `0.2.580` for
the general interop and preparation APIs:

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

By default a non-Init import must belong to the captured local DAG. An explicit
finite installed module closure can be permitted with repeated
`ProjectOptions.Builder.installedImport("Lean.Data.PersistentHashMap")`, or
`:installed-imports ["Lean.Data.PersistentHashMap"]` in Clojure. This resolves
only exact module names in the configured trusted sysroot, snapshots their
compiled products (including optional-file absence), and binds those identities
to cache and artifact provenance. Every transitive non-Init installed dependency
must also be listed. It grants no additional runtime capabilities or initialization
support; unsupported builtin/anonymous initialization still fails. See the
[unchanged persistent-map workload](examples/persistent-map/README.md).

External package fetching,
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
compiler layout evidence. Select one to 1,024 entry names per project with the current producer. Older
producer bundles retain their 16-entry preparation limit. This count is
independent of function arity; dependency, byte and execution budgets still apply.
Discovery does not automatically admit every declaration in a module.

This table describes the legacy v1/v2 carriers. The v3 path described below adds
shared typed container and byte views; old prepared artifacts keep their carriers.

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

See [JVM and Clojure value examples](VALUE_EXAMPLES.md) for nested carriers and
Java varargs calls. The [preparation guide](PREPARATION.md) covers build-time
artifact export through the Java/Clojure APIs and CLI.

The [pure FFI candidate](FFI.md) selects Java/Clojure implementations for checked
noinline Lean reference definitions, using the same value boundary. It includes
general arity and type-driven factories for custom results. V4 source producer
publication and release are pending; existing v3 loading remains unchanged.

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
use named calls if several exist. The [supplied-stdio guide](STDIO.md) describes
`LeanFunction.invokeWith(InvocationOptions, Object...)`, `LeanProject.callWith`
and Clojure `call-with-options`: finite per-call stdin and exact byte captures,
with text convenience views. Existing calls use empty input. A data codec does
not implement arbitrary IO: the current task-free runtime has a limited audited
intrinsic set. Unclassified required externs are refused before startup. Declared terminal
traps and unsupported dynamic captured-stream operations can fail when reached
at runtime.

The [proof-backed insertion-sort example](examples/fp-lean-sort/README.md) runs
the complete unchanged upstream module through explicit monomorphic IO adapters.
Its `dbgTraceIfShared` operation checks actual managed objects/immediate scalars
when executed. Java String and BigInteger heap-leaf sharing observations remain
unsupported and throw if reached. Admission does not promise every input or path
can execute: earlier guest work can occur before such a failure, and the failed
Project must be closed rather than reused. This replaces the earlier conservative
pre-startup provenance analysis; source, artifact and full-ABI checks remain.
Diagnostic output is captured on stderr; pure checked entries still reject it.

Uncaught Lean IO errors throw `LeanException` with code `GuestIOError`. Its
immutable `details()` map currently exposes authenticated `userError` messages as
`{"kind": "userError", "message": "..."}`. Messages are limited to 2,048 UTF-16
units without splitting a surrogate pair; `messageTruncated: true` marks clipping.
Other error variants keep empty details. This is a partial error projection;
the v3 datatype boundary does not expose arbitrary IO.Error internals. Host cancellation and resource limits remain
terminal host failures rather than catchable Lean exceptions.

With the new v3 producer, supported entry-reachable enums, records and ordinary
recursive datatypes have the automatic boundary below. Open polymorphic,
implicit/dependent, proof-bearing or higher-order host arguments, indexed or
mutually recursive families, nonuniform recursion, constrained
Fin/Vector/Subtype/Rat adapters, function-valued callbacks, task/resource fields, cyclic values,
and public forks remain unsupported. The
[release checks](RELEASE_CHECKLIST.md) distinguish follow-up work from this boundary.
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

### Automatic datatypes with the v3 producer

The new v3 source and artifact path discovers supported closed types, constructors
and fields from native declaration, callable and compiler-layout evidence.
Application authors supply entry names, not handwritten datatype bindings. The
three-file [expression application](examples/datatypes/README.md) defines an enum,
recursive tree and mixed record across `Syntax`, `Eval` and `Main`; see
[value examples](VALUE_EXAMPLES.md#automatic-datatype-values-v3) for Java and Clojure.
This path requires the reviewed [v3 producer](producer/README.md#datatype-v3-producer).
Published v1/v2 conventions and byte-array copies remain unchanged.

V3 handles expose detached `LeanType` metadata through `argumentTypes()` and
`resultType()` when `hasTypeMetadata()` is true. Their public `descriptor()` also
contains actual `LeanType` objects for arguments and result, rather than internal
graph indices. Old handles report false and these metadata accessors throw
`UnsupportedSignature`; reprepare with v3 to acquire metadata.

Nominal Java results are immutable `LeanData` values with structured constructor
Names and ordered logical fields. Clojure returns immutable tagged map views
with `:lean/type`, `:lean/constructor` and `:lean/fields`; nested containers use
views too. V3 bytes are immutable `LeanBytes`; `toByteArray()` explicitly copies.
V3 Clojure Char results use characters for BMP values and scalar integers for
supplementary values. Typed conversion depth is bounded at 1,024; the legacy
recursive conversion path retains its depth-128 limit.
Use `LeanType.materialize(value)` in Java or `lean/materialize` in Clojure for
ordinary collection/byte snapshots. These detached values remain usable after
Project close and can enter a fresh compatible Project. Compatibility requires
matching logical type, defining-product identity, representation and runtime
value-class cohort. Editing a defining module conservatively invalidates its
values even when its declaration Name or apparent layout stays the same.

First export validates and freezes the unique reachable graph without copying
its data payload. Reimporting a certified compatible root uses stored bounds
instead of rescanning that graph. Field access can allocate views or boxes;
construction, first validation, equality and materialization have real costs.
This is not a zero-allocation or zero-first-crossing-cost guarantee.

All explicit arguments share one preflight budget outside the execution lease.
Java argument validation reports `InvalidArgument`; Clojure literal conversion
can reject with `IllegalArgumentException`. Combined input quotas report
`ResourceLimit` before guest effects, leaving the Project reusable. Shared
certified root frontier counts once; distinct overlapping frontiers can be
conservatively overcounted. IO custom-data success freezes only its pure
payload and releases the IO envelope. Uncaught guest IO errors retain the
existing terminal Project policy; immutable returned values remain readable.

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
checks and standalone resource checks against the same compiled engine. Its launcher
requires Java and javac 17 or later and uses bounded sequential JVMs. Source
compiler helper provisioning is not part of mandatory SDK CI. The main-only SDK
deployment job receives the exact checked JAR/POM/release receipt through the
workspace and deploys verified bytes without rebuilding. GitHub release waits
for both core and optional Clojars deployment.
