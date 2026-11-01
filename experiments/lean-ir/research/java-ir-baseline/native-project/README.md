# Official frontend → Java IR entry

This research profile runs the unchanged selected FP Lean first-Lake tutorial
using the official pinned native Lean checker/compiler and the same Java IR
runtime as the hosted campaign. Native frontend installation is an explicit
dependency. This does not establish hosted default Init, Java kernel checking of
this compilation, arbitrary Lake packages or full module-initializer parity.

The intended project API owns compilation and caching internally: callers supply
a project path after configuring the toolchain once. An internal exported artifact
is not an extra concept Java callers must learn. The current `prepare!` API is a
research integration seam; public Java API design and release packaging remain
separate work.

The [Java API proposal](JAVA_API_DESIGN.md) makes the intended caller experience,
project lifetime, checked type evidence and kernel-store reuse concrete for
discussion. It is design only and adds no public implementation.

The separate [typed bridge probe](typed-bridge/README.md) exercises actual native
CI/type/callable evidence for pure Nat and String entries on one reusable explicit
engine. Its model and execution receipts do not establish module startup or a
general public Project API; the ordinary loader does not activate that registry.

`runner.clj` is byte-identical to the parent-tested ignored implementation,
SHA `ea4502d5a9ab79cbd340155142dc8919ccdcb3291ad018ff871dde45793bff76`.
Load it once with `loader.clj`; never reload its opaque Artifact/Run registries.
For a retained process that already loaded that exact implementation, load only
new model definitions. Definition loading opens no compiler, artifact or engine.

The trusted native-build importer checks an independently supplied manifest pin,
all bounded bundle file hashes, the exact three source hashes, actual empty local
initialization plans and the accepted six-row execution stream. It preserves
actual runtime roles, reserves canonical same-source Headers before materializing
bodies and rejects missing dependencies, redirected/initialized rows and
unreviewed externs. The exact pinned native build is the authority here; a caller
map or SHA alone is not a native build, signature or Java type-check certificate.

The selected `main : IO Unit` type comes from the fixed source annotation actually
checked by native Lean. Its erased raw ABI (`void` → `object`) is only a calling
convention. A generic typed-function API will need actual checked entry-type
evidence rather than inferring a Lean type from that ABI.

`execute-io-unit!` creates a fresh inactive engine from the prepared immutable
Program, invokes actual main, validates actual IO.ok Unit, captures stdout/stderr,
releases its owned result and closes normally. Inactive synchronous close yields
`closed=true`, `disposed=false`; this is distinct from active-runtime disposal.
Failure returns an opaque Run in exception data so its actual engine/result
journal remains inspectable; it does not retry or silently unwind.

The static closure contains one dynamic AP through the genuine stdout Stream
method. It is not a proof of arbitrary dynamic dependency closure. Closed String
values use existing runtime cache semantics; no expected greeting is synthesized
by a host callback. Nonselected imported Init initialization is outside this
entry-closure profile. All selected source initialization plans are genuinely
empty; future initialized values must be handled explicitly rather than relabelled.

The parent actually loaded the frozen profile into the retained 512 MiB JVM,
prepared the producer artifact, and observed IO.ok Unit, exact fourteen-byte
`Hello, world!` plus LF, empty stderr, native reference parity and normal
synchronous close. The portable provenance and receipt locators are in
`manifest.json`. Models are separate pure admission checks, not execution evidence.

The exact source selection, upstream attribution and 4.33.0→campaign4.33.1
toolchain distinction remain in [the tutorial target](../tutorial-demo/README.md).
Source files are not vendored by this package. Public Java packaging must still
bundle or replace the helper/toolchain adapter; the Python prototype is not a
promise of a mandatory Python dependency in the Java release. A bounded source-helper
`lean --run Export.lean` probe exceeded 900 MiB without output, so that fallback
has not been established under the current cap.

## Project-path prototype

Load the separate `service.clj` definitions once after the runner. Configure
`native-project-service-v1/configure!` once with the Java basis, installed
official sysroot/exporter and private cache. New Loaders default to the internal
JVM compiler backend and invoke no Python. The loader defines the compiler
namespace before the service; do not reload either opaque registry beneath
live tokens. The [JVM compiler checkpoint](JVM_COMPILER.md) records its process
limits and separate validation status.
Then `load-project!` accepts only that Loader and the unchanged project directory;
it owns the actual subprocess/cache invocation and artifact authentication.
Execute the returned `:artifact` through `execute-io-unit!`. Callers do not run
export commands or manage module build order themselves.

The optional `:native-reference?` flag requests a native comparison execution as
part of this selected tutorial's validation build; default false does not run
the native program. Its absence must not be read as fresh native parity evidence.
Explicit `:backend :python` retains the older research service and requires its
pinned Python/helper inputs. Already-issued Python Loaders retain their original
backend. No failure falls back between implementations. Bundling the native
helper and a public Java facade remain separate release work.

The loader invokes pinned code without a shell, confines returned artifacts to
its private cache, bounds process wait/output and checks semantic `ready` before
opening any Java engine. Compiler failures stop any still-live owned process, preserve interruption and
the actual process handle alongside stdout/stderr journal paths
and cannot fall back to another execution backend. The trusted installed sysroot
is explicit; its reported version and path/stat descriptor are mutation guards,
not full byte attestation of every library. Cache publication/hit verification
belongs to the actual pinned service and is recorded separately from JVM runtime
execution. Current profile and supported source set remain deliberately finite.

## Validation boundary

The parent tested these exact runner/client sources in the retained 512 MiB JVM:
entry models passed six tests / 29 assertions, and the corrected process-client
models passed four tests / 14 assertions. The Python service's seven metadata,
cache and small-process checks also passed. These model results are separate
from program execution evidence.

The earlier Python-backed project-path client selected a validated cache hit, authenticated and
prepared the canonical Program, then ran main to IO.ok Unit, exact native output
parity and ordinary synchronous close. No manual export step was required by
that call. The standalone Python service had previously passed a real cold
compile and cache hit, with five native stages totaling 6.60 seconds and sampled
peak RSS 672,284 KiB. The complete cold path through the JVM wrapper was **not
run**: its preflight found about 1.7 GiB available, below the 2 GiB floor, and no
native job was started. A service cold run plus a wrapper cache hit must not be
reported as a tested wrapper cold run.

The earlier JVM compiler checkpoint passed eleven model families / 55 assertions, then actual
cold compilation, a cache hit with identity probes only, and entry execution to
the same native output with zero Python invocations. The later default Loader
also passed cold compilation, a cache hit and entry execution on its exact
source checkpoint. See the
[compiler checkpoint](JVM_COMPILER.md) for exact source/receipt pins, measured
resource use and preserved failure history. A bounded RSS-resampling follow-up
changes source/cache identity again and awaits its own validation.

Portable validation summaries, source hashes and external research-receipt
locators are recorded in `manifest.json`. This landing work introduces no
hosted Init, Java kernel rechecking, generic Lake-project acceptance or public
Java facade. It includes neither an Init image/store nor the unrelated source,
kernel or bootstrap implementations used by the wider research campaign.

The next bounded local-project profile is specified in the
[general project plan](GENERAL_PROJECT_PLAN.md). Its
[source review gates](SOURCE_REVIEW_GATES.md) cover genuine Init startup,
portable entropy, atomic arithmetic limits, failed-branch lifetime, deferred
fork and Java packaging. These documents state requirements and decisions;
they do not extend the accepted fixed tutorial profile.

A separate tiny-greeting measurement reused the prepared Program while creating,
validating and closing a fresh engine on every invocation. After 30 warmups,
100 samples had median 69.415 microseconds and p95 457.489 microseconds, with
about 26,592 thread-allocated bytes per call. Compilation/cache loading is
excluded. This is evidence of repeated invocation without an image/Prelude
reload, not a general Lean performance comparison.

## Internal local module compiler preparation

`local-project.clj` adds a separate `native-local-project-prepare/2` path. It
captures exact UTF-8 bytes for reachable ordinary local modules, invokes the
source-pinned `NativeStartupEvidence --header` producer, validates the original
implicit Init pair and explicit import provenance, preserves duplicate import
occurrences, and schedules the structural typed DAG in stable dependency order.
`prepare!` returns planning metadata. `compile-modules!` also uses the separately
pinned typed source exporter and validates each genuine local stream, module
identity, direct imports and source origin. Neither function issues an entry,
runtime artifact, startup receipt or ready Project.

The opt-in helper `lean/TypedSourceExport.lean` is a mechanical copy of the
accepted `lean/Export.lean` at SHA-256
`3311d15c99dc91b599771e328475f2a65a70a0c4fe4c71bfe82b1c2883499f95`.
The only semantic changes are a bounded structural string-Name decoder and a
strict source/local/output command shape. Original frontend invocation, IR row
encoding, dependency emission, runtime roles, exports and source initializer
observations remain unchanged. The accepted exporter is untouched. The new
helper accepts:

```
--source SOURCE --olean OUTPUT --local --typed-module STRUCTURAL_NAME_JSON
```

Arguments are separate `ProcessBuilder` elements. A string component containing
a dot remains one component; no dotted-name parser is used for module identity.
Numeric module Name components are rejected. This helper is source compilation
transport, not checked-entry or ordinary-startup evidence.

Both functions take the actual configured fixed compiler, an explicit
configuration map and a fresh journal atom. Required configuration fields are
`:project`, `:source-root`, `:roots` (bounded vector of structural module Names),
`:helper`, `:helper-source`, `:helper-sha256` and `:helper-source-sha256`.
`compile-modules!` additionally requires `:typed-exporter`,
`:typed-exporter-source`, `:typed-exporter-sha256` and
`:typed-exporter-source-sha256`. These independently reviewed pins are trusted
compiler configuration; an arbitrary caller-produced Header JSON is never
accepted in place of an actual monitored helper run.

The manifest-last `lean-local-compiled-modules/2` cache binds captured source
records, ordered typed edges/roots, implementation, helper/exporter and installed
toolchain descriptors. Reuse validates the complete bounded file set before
using compiled products. A hit still performs native header preparation and
toolchain checks; it skips native local-module compilation. This is not a claim
of zero native processes on a cache hit. Entry evidence, full static union,
ordinary startup, capability admission and Project lifetime remain subsequent
release gates. The fixed tutorial compiler and its artifact reader are unchanged.

`local-project-models.clj` contains structural negative models. Synthetic Header2
records in those tests are deliberately model data, not native acceptance
receipts. Native/JVM execution and integrated acceptance remain with the root
review runner; do not infer a run from source presence.
