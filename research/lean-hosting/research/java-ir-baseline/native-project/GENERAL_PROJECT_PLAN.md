# Bounded local Lean projects through the native frontend

Source-only implementation contract, 2026-10-31. This is not acceptance evidence
or a change to the frozen tutorial compiler. No JVM, native compiler or artifact
export was performed for this plan. The [source review gates](SOURCE_REVIEW_GATES.md)
record the agreed entropy, resource, lifetime and release decisions; none of
those requirements is implemented merely by this document.

## Recommendation

Implement a new internal `native-local-project-v2` profile beside the fixed
tutorial profile. It captures a bounded ordinary local module DAG, lets the
pinned official Lean frontend check and compile those exact bytes, obtains
native checked entry evidence, prepares one immutable canonical Java Program,
executes the complete admitted interpreter startup plan, and only then issues a
ready Project. Keep the existing backend/artifact reader unchanged.

The smallest coherent next PR is this internal compiler/artifact/Project path
with explicit roots, up to sixteen requested entries, and three admitted entry
signatures: IO Unit main, Nat → Nat, String → String. Include ordinary implicit
Init initialization even for a pure entry. Do not ship a general project claim
by deleting the tutorial hashes while retaining its six-row/empty-startup
assumptions. Public Java names, generic Lake dependencies, hosted Init, matching
kernel stores and version bridges remain separate work.

## Existing authority and missing seams

Pinned toolchain: Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, 64-bit
`x86_64-unknown-linux-gnu`. Installation remains an explicitly trusted immutable
dependency; reported githash/version and stat/hash descriptors are mutation and
provenance guards, not cryptographic attestation of the full sysroot.

Inputs inspected:

- [Java API proposal](JAVA_API_DESIGN.md)
  and the frozen JVM compiler/cache protocol.
- [NativeEntryEvidence source](../../../lean/NativeEntryEvidence.lean), inspected in the source-module integration checkout at commit
  `ad00631df2cd2ba071752acff29825e075f9e4e4`, SHA-256
  `e89beefe6ebb864d830367a377360d68cbce89c97fa6a5a5e9dab8877b6c6629`.
- the tracked [compact startup plan](../startup-evidence/PLAN.md) and its
  [actual saved-Init census](../startup-evidence/census.json) and
  [canonical closure census](../startup-evidence/closure-census.json). The
  original ignored-plan snapshot used during drafting had SHA-256
  `2ec84730ac379b019f91b5d86f8f8f0149d908b09f80b291389a717fa6fad4ce`;
  the tracked proposal preserves that lineage with its own byte inventory.
- Pinned upstream `src/Lean/Elab/Import.lean` (`HeaderSyntax.imports`),
  `src/Lean/Util/Path.lean` (`modToFilePath`/`findLean`),
  `src/Lean/Compiler/InitAttr.lean` (`runInitAttrForMod`) and
  `src/library/ir_interpreter.cpp` (`run_init`).

The accepted entry helper is sufficient for authentic header interpretation and
entry CI/boxed-callable evidence. It is NOT an ordinary startup producer:
`--entries` deliberately imports its requested module with private visibility,
importAll=true and isMeta=true, and explicitly labels its initialization inventory
as not-execution. A new source-pinned startup helper must capture the actual
ordinary effective import profile; never reinterpret the existing inventory.

The new initializer publication seam is narrow: named regular init, initialized
object/tobject global, action owned void → object, actual successful IO payload
made persistent and published by identity. Anonymous actions, builtin effects,
module-entered ledger and entropy remain distinct obligations. ByteArray.get!
and entropy admission must be completed before claiming ordinary Init readiness.

## 1. Configuration and source selection

Internal input, not a new public Java class:

```
compile-project! Compiler
  {:project Path
   :source-root RelativePath
   :roots [TypedModuleName ...]
   :entries [{:name TypedConstantName :signature :io-unit|:nat-to-nat|:string-to-string} ...]
   :profile :legacy-local-init-v2}
  journal
```

Configure sysroot, both independently pinned helpers, cache and runtime
capability policy once. A signature is a request, never proof. Roots select
compiled environments, not a guessed prefix for locating a constant. Entry
evidence must attribute every exposed entry to an actually compiled local module
in that root closure. Initially reject sysroot-owned entry handles.

TypedName is the producer's structural anonymous/str/num Name transport, with
exact string components and canonical nonnegative decimal numeric leaves within
the helper's admitted UInt64 range. Preserve its depth/text bounds as well.
Preserve those tags and leaves; a string leaf "7" is not a numeric leaf 7.
Dotted convenience accepts string components only and never parses numeric
segments. Module paths reject Name.num; expert constant requests may retain
numeric Name components only through the exact typed transport. Never authorize
an entry by its displayed dotted name or a guessed owner prefix.

For `loadProject(path)` convenience, accept a data-only `lakefile.toml` adapter
with one unambiguous executable root or explicit options. Parse TOML using a
real bounded TOML parser, not regex or Clojure reader. Preserve exact TOML bytes.
Recognize only the declared subset (package name, source directory, library and
executable roots); reject dependency requirements, custom build arguments,
scripts/plugins and unknown semantic fields. Do not run Lake. A `lakefile.lean`
requires explicit refusal, not evaluation. Multiple candidate executables require
an explicit selection before compilation. Explicit configuration is sufficient
for the first internal PR; TOML convenience must not silently guess its schema.

Capture exact valid UTF-8 bytes into an exclusive private build directory.
Preserve LF/CRLF, BOM, Unicode and comments; no normalization or header rewrite.
Exclude `.lake`, `.git`, caches and build products from discovery. Reject
symlinked components, path escapes, special files, duplicate/case-colliding
relative paths, overlapping roots and ambiguous module-to-file associations.
The project source is a trusted native-compilation input, not a sandboxed
untrusted program: native Lean can execute metaprograms/compile-time IO. "No
plugins/network dependencies" means no Lake scripts, package fetching or supplied
native plugin dependencies. It is not a security guarantee that source code
cannot perform effects while the official frontend runs.

Initial limits: 128 selected local modules, 1 MiB per source, 16 MiB total
source bytes, 64 KiB data-only project configuration, 2,048 direct local edges,
depth 64, sixteen selected entries, 4,096 imported modules. All are preflighted
on actual bounded vectors/bytes; do not realize an unbounded caller sequence.

## 2. Original header discovery, typed identity and topological build

Invoke actual `NativeEntryEvidence --header` on the captured file. Bind its raw
output to that file's digest and actual helper/toolchain receipt. Validate
schema, target/compiler identity, sourceUTF8Bytes, disabled normalization,
bounded parserEndByte and typed requested imports. Do not parse Lean imports
with regex, split source lines or use filename display text as import proof.

`HeaderSyntax.imports` already inserts BOTH ordinary Init and meta Init when
there is no prelude. Preserve these requested occurrences and their flags; do
not append another implicit Init, deduplicate them in source evidence, or reject
the original implicit pair as a user meta import. For this first profile reject
module-mode headers, explicit meta/all imports, prelude-only profiles and
nonstandard requested flags. An exact ordinary header with its actual implicit
Init pair is admitted. The current header schema does not expose prelude or
explicit-vs-inserted provenance, so these syntax restrictions require a NEW
source-pinned project-header/2 mode exposing actual HeaderSyntax prelude and
explicit import nodes/flags alongside the existing interpreted list. This is a
small required producer seam, not an inferred fact already in --header output.
Keep the accepted header/1 producer unchanged. Do not infer that distinction by
searching source text. Alternatively a separately reviewed profile could admit
semantically equivalent explicit header forms; do not silently widen this one.

Resolve each exact typed import against the configured source root or the
installed `Init` namespace only. Use pinned `Lean.modToFilePath` semantics:
anonymous is the base path, Name.str appends one literal filesystem component,
Name.num is invalid for an import. Reject slash/backslash/NUL, absolute or
dot/dot-dot components before any path operation. A quoted dot inside a string
component is not a numeric leaf or an instruction to split it. Validate the
canonical contained path, exact extension and actual native-compiled module
identity. Prefer adding a bounded native resolver result to the helper if a
Java port cannot preserve this exact mapping. No cwd/ambient LEAN_PATH lookup.
Local code cannot shadow reserved Init names. Any other sysroot/package prefix
is an explicit unsupported external import, not a request to fetch it.

Keep exact ordered requested-import lists, including duplicate occurrences.
Deduplicate only graph scheduling by typed module identity. Detect cycles with
a bounded DFS and report the actual typed cycle/path. Preserve each module's
direct-edge order. Build dependencies first, once per snapshot, using a stable
root-order traversal. Merely finding a `.olean` beside source is not admission:
use only products built from this captured closure or fully validated cache
products. Imported `.olean` provenance binds exact source/dependency hashes.

Run the existing source exporter per local module with private copied sources,
explicit module identity, private `.olean` output and LEAN_PATH consisting of
this build root then the pinned sysroot. Preserve its exact local stream,
sourceLocal flags, roles, exports/redirects and initialization plan. Do not mark
inherited rows local. Compare the producer's actual direct/imported identities
to the discovered graph; a mismatch fails compilation admission.

No synthetic aggregator Lean file is necessary. For independent roots, export
entry evidence in each genuine root environment and combine only exact-equal
canonical rows. If startup needs a union environment, its producer accepts the
actual ordered root import array directly, rather than fabricating user source.

## 3. Checked entries and immutable value codecs

Use original `--entries` requests (one to sixteen, at most 64 KiB) after native
compilation. Retain the raw output. The consumer validates every requested Name
appears exactly once and checks the actual CI kind, no universe parameters,
closed type, admitted safety and actual local-module origin. Native
`Lean.Meta.isDefEq` at default transparency must have established the exact
requested supported type. Preserve actualType and expectedType structural Expr
evidence; neither the request signature nor a self-authenticating JSON boolean
is authority. The trusted native build receipt binds that helper output.

Preserve original raw declaration and callable from
`lean_ir_find_env_decl[_boxed]`, including the base-module-index lookup result.
No `_boxed` suffix guess, name flattening or ABI-only type inference. Each entry
binds exact source CI Name, callable Name, raw/boxed ABI, owned argument plan,
actual raw row digest, canonical Header, code cohort and ProjectVersion. All
Headers are reserved before bodies are materialized. Same Name with different
canonical rows/roles/source origin across outputs is a conflict, not first-wins.

Public-facing conversion contracts for the eventual facade:

- Nat → Nat: accept an exact immutable nonnegative BigInteger, check the
  configured bit bound before changing guest owners, encode values ≤Long.MAX_VALUE
  as canonical nonnegative Long and larger values as immutable BigInteger.
  Do not accept an arbitrary Number or silently narrow a big Nat. Decode only
  actual nonnegative Long/BigInteger carriers to a complete BigInteger result.
  BigInteger subclasses require an explicit defensive-copy policy, not an
  assumption of immutability. Initially exact-class admission is simpler.
- String → String: accept actual immutable Java String, reject unpaired UTF-16
  surrogates before guest work, bound encoded UTF-8 bytes with a REPORT encoder,
  preserve NUL/Unicode/combining sequences exactly and perform no normalization.
  Decode only an actual String and validate the same scalar/size invariants;
  never `toString` an arbitrary Node or replace malformed bytes silently.
- IO Unit main: caller supplies no arbitrary object/world; pass canonical erased
  Unit through the exact source-backed callable plan. Validate the actual owned
  IO.Result wrapper, success tag, one-field/no-scalar shape and Unit payload0.
  IO.error remains a real owned IO.Error result, not a String or fake success.

Suggested initial codec limits: 65,536 Nat bits and 1 MiB UTF-8 String argument/
result. These are explicit profile limits, not truncation or Lean type limits.
Result validation does not replace intermediate allocation bounds. A Node is
never returned as an ordinary Java value. Prepublish the result owner slot before
take, convert/copy while ownership is known, then discharge the actual result
through the admitted release protocol. Rejection of a Java argument must leave
entry counters, entropy, module state and guest ownership unchanged.

## 4. Artifact contract and complete selected code

New schema `lean-native-local-project/2`; do not mutate the fixed v1 reader.
Manifest-last, relative-path-only, bounded exact file set:

```
producer {leanCommit, leanVersion, target, helper/source/binary cohort, options}
inputs {profile, configuration, capturedSourceDAG, installedToolchainDescriptor,
        requestedRoots, requestedEntries, runtimeCapabilityPolicyDigest}
modules [{name:TypedName, source:path+hash, rawHeader:path+hash,
          requestedImports:[actual tuples], directLocalDependencies:[TypedName],
          olean:path+hash, localStream:path+hash}]
entryEvidence [{rootModule:TypedName, raw:path+hash, entries:[evidence refs]}]
startupEvidence {raw:path+hash, actualProfile, moduleOrder, selectedActions}
code {canonicalRows:path+hash, constituentRawOutputs:[path+hash],
      actualStaticRoots:[TypedName], dynamicAPSites, dynamicClosureProven:false}
capabilities {requiredActualABIs, configuredProviders, unresolvedDynamicFrontiers}
files {relativePath:{bytes,sha256}}
trust {frontend:"official-native", javaKernelChecked:false,
       hostedInitImported:false, startupExecutionReceipt:false}
```

Actual startup receipts and live runtime readiness are NOT stored in a reusable
compiled artifact. They belong to each new engine branch. Preserve type/IR
evidence and imported order in raw producer form as well as bounded projections.
The trusted compiler returns the expected final manifest digest directly to the
artifact issuer; external loadArtifact requires an independent expected digest
or reviewed distribution trust. Hash equality is not a signature.

Union all selected entry/raw/boxed, required guest-export implementation, redirect,
initializer action and initialized-global roots. Preserve all rows on error/
panic branches. Complete static dependency closure is mandatory. Existing helper
limits remain: 2,048 rows per evidence request, 32,768 pending names, 16 MiB raw
producer output. Start v2 with at most 4,096 distinct union rows/64 MiB total
artifact and fail explicitly beyond that; widening is a separate measured gate.
Entry and startup outputs must agree byte-for-byte on overlapping declarations.
Preserve runtime role and source origin. Never invent a body for an initialized
global, replace a missing initializer with an ordinary constant, or deduce empty
initialization from the selected entry's static code.

## 5. Ordinary Init startup is unconditional

For the first legacy profile obtain an actual startup environment for the
ordinary requested project roots at global/private level. Capture actual
EffectiveImports, module/header mode, options and phases, not a caller-written
"ordinary" tag. Bind this evidence to the same source/olean/toolchain cohort as
entry evidence. The existing entry helper's more permissive import profile must
not determine runtime phase decisions.

Walk actual env.header.modules order, including modules with empty lists. For
each module preserve regular/builtin module entries and IR entries. Recompute
the source sequence: preserve the first regular list exactly; append IR entries
not contained in that first list; apply the actual initRuntime/IR-phase rule.
This is not an arbitrary whole-list set deduplication. Builtin arrays are not
appended to the regular loop. Require empty builtin obligations for the initial
admitted profile or a separately reviewed exact native-bootstrap substitute.

Every ordinary Init project must execute the actual selected Random initializer,
even if entry code never reads randomness. Current saved Init evidence has 631
modules and the same IO.stdGenRef named pair in private/IR lists, selecting one
action. That census is a target expectation, not permanent hardcoded authority:
the actual freshly imported profile supplies the lists and order. Do not claim
captured-global presence proves module initialization, skip unreachable actions,
or relabel the old tutorial's entry-closure behavior as ordinary Init parity.

Before engine creation classify ALL selected actions. Named globals require
native checked equality `actionType = IO targetCI.type`, exact target/action
Names, original callable mapping and admitted object/tobject global plus owned
void→object action ABI. Initially reject anonymous regular actions and nonempty
builtin obligations with the exact module/tuple and required capability. A later
anonymous IO Unit path uses its own ledger and actual result ownership; never
fabricate a dummy global to reuse named publication.

Project startup state is a private issuer ledger, not a caller map:

```
NEW -> STATIC_PREFLIGHTED -> STARTING -> READY -> CLOSED
                              |-> FAILED/CANCELLED (no entry, no replay)
module: UNENTERED -> ENTERED -> SUCCEEDED | FAILED | CANCELLED
action: UNSTARTED -> RUNNING -> SUCCEEDED | FAILED | CANCELLED
```

Mark a module ENTERED before its first action, even for an empty module. Resume
pending actual Host/Code/result tokens; never restart an action. A named action
uses actual Engine.startInitializer/advance/completeInitializer, validates the
real IO.ok status, releases it, and witnesses the same persistent global payload.
IO.error/failure/cancellation prevents Project readiness. Only after all selected
modules/actions succeed call finishInitialization. New compiled artifacts are
reusable; an engine's entered ledger is not reusable as another engine's proof.

Random requires genuine bounded entropy and exact ByteArray/UInt64/Ref behavior.
Its action requests eight bytes. V1 chooses portable JDK entropy with actual
IO.Error.userError on expected provider failures, bounded truthful details and
no fabricated POSIX errno. Tests can inject clearly labelled deterministic bytes.
Unsigned cap/zero-no-effect admission, pre-read journaling, engine-owned ByteArray
creation and host cancellation/VM-failure handling follow the
[entropy review contract](SOURCE_REVIEW_GATES.md). Publish the actual resulting Ref once, preserve it
across repeated calls, and never reseed on a cache hit/function call. The startup
helper may itself execute native initializers while importing modules; record
that as native build-time behavior, distinct from Java branch startup.

## 6. Capability preflight and runtime lifetime

Before creating an engine, validate every actual IR operator, typed lane, exact
extern symbol/ABI/borrow mask, guest-export target, role and static dependency
against the selected runtime Class/cohort and explicit provider policy. Reserve
guest origins before conflicting HostExtern descriptors. No generic "symbol
exists" approval: action-profile requirements and boxed/borrowed entry fences
also matter. No complete-catalogue hydration, dummy startup, native fallback,
manual source rewrite or headerless Program extension.

Static preflight can reject known missing capabilities before Java effects; it
cannot prove arbitrary dynamic AP targets or data-dependent budgets. Record AP
sites and admitted constructor/stdio factory policies. Unsupported dynamic
boundaries stop with the actual packet and owner journal. Unknown code cannot
be fetched from an unrelated catalogue. Never report all runtime failures as
pre-effect just because the build was statically complete.

ProjectVersion owns immutable admitted artifact/Program/entry evidence. Project
owns one thread-confined serialized explicit engine and its startup/global/stdio
state. Repeated calls reuse them: no compiler, header reparse, init replay,
classloader or fresh engine per call. Entry handles bind that actual version and
lease. Closing serializes with calls, releases known owners while services are
available, closes the engine/resources and invalidates handles. Preserve the
reviewed Compiler close/wait registry fence. No weak-map value may point back to
its opaque key through journals or issuer holders.

Use explicit start/advance/take with host-controlled quanta, instruction/work,
deadline, output and allocation policies. A valid IO.error has genuine result
ownership; an unknown Host/Code request, terminal exception or cancellation
retains actual custody. No automatic entry retry or fresh-engine replay after
effects. A normal teardown or honestly labelled restricted-profile abandonment
policy must exist before a public release; active frames are not normal close.
Keep failed branches unusable. A native-build process failure never creates or
unwinds a Java guest engine.

Important separate runtime risk: Nat.pow performs repeated BigInteger
multiplication and an IR instruction budget does not bound one intrinsic's
allocation/time. Input codec caps do not bound intermediates. The required
[atomic-operation review gate](SOURCE_REVIEW_GATES.md) adds overflow-safe bit/work
guards before allocating Nat.mul/pow/shift results and polls between pow steps.
These remain cooperative limits, not hard heap/deadline guarantees. Similar
audits are needed for other growth operations, large strings/arrays and dynamic
callbacks. The compiler/artifact slice can land separately; public generic
execution needs those runtime and failed-branch lifetime gates first.

## 7. Compile cache, invalidation and repeated REPL work

Use separate discovery/compilation and prepared-runtime caches. Portable build
key = canonical source relative paths+byte hashes, typed DAG and actual ordered
import flags, data configuration, selected root/entry requests, supported
signature/type-check policy, all helper source/binary hashes, compiler source/
options, target and trusted installation descriptor. Include startup producer/
policy identity. If runtime-dependent filtering changes artifact contents,
include that policy/cohort too; otherwise keep raw portable code and key the
separate prepared Program by actual runtime Class and capability policy.

Warm source/byte inputs still require capture/revalidation. A build hit probes
and verifies the installed dependency descriptor under the resource floor,
rehashes the bounded exact file set and validates every semantic binding. It
does not execute startup or provide a module-ready receipt. Loaded Project call
reuse performs NONE of those compiler processes. A source change creates an
explicit new version; old live handles stay bound to old code. Additional entry
selection is an explicit new evidence/version operation, not mutation of an
already issued handle or unchecked suffix lookup.

Preserve JVM ProcessBuilder ownership: shell-free invocation, actual handle
published before waiting, actual/observed descendant RSS and count bound,
bounded pseudo-file sampling, CPU/core/file hard limits, MemAvailable floor,
per-command and whole-build wall/output limits, interruption restoration,
known-process cancellation and diagnostic retention. One native process at a
time per configured compiler; cross-compiler scheduling belongs to a bounded
shared service, not an undocumented promise from separate per-token locks.
Start with current 900 MiB sampled process-tree cap, 2 GiB available floor,
90 CPU/120 wall seconds per command, and 600 seconds total build wall time.
These are Linux research policies, not a portable sandbox. Manifest-last and
same-filesystem atomic publication remain; an existing winning entry must
independently validate. No automatic alternative backend on failure.

Keep cold and hit receipts separate. Preserve native reference comparison as an
explicit user/test option: compiling or loading a generic project must not
silently execute its main natively. Only record fresh native parity when an
actual separately journaled native run occurred. Cache/stat provenance may use
absolute installation paths; shipped guidance and portable manifest payload
paths must not contain developer checkout paths.

## 8. Explicit errors and minimum acceptance

Use stable host envelope codes at actual boundaries:

| Code | Facts to retain |
| --- | --- |
| UnsupportedProjectConfig | exact config field/path, no Lake evaluation |
| HeaderRejected / NativeCompileFailed | actual helper stage, module/source digest, exit and bounded raw diagnostics |
| ExternalImport / ModulePathConflict / ImportCycle | exact typed Names, original flags and actual contained paths/cycle |
| EntryRejected | exact requested Name/signature, actual native helper diagnostic/evidence boundary |
| ArtifactConflict / MissingDependency | exact row hashes/Names/source outputs |
| UnsupportedStartup | actual module/index/tuple/category/phase and required ABI |
| CapabilityMissing | actual Header hash, symbol, full ABI and missing policy |
| BuildResourceLimit / Cancelled | actual process/stage/journal; no success artifact |
| RuntimeBoundary / InitializationFailed | actual engine/entry/action packet and preserved private owner journal |

Do not invent line/column or severity from diagnostic text. Use original native
MessageLog/FileMap data when the helper actually exports it; otherwise retain raw
diagnostics and stage/source attribution. Lack of structured diagnostics is an
explicit first-version limit, not permission for regex categorization.

Minimum next PR changes: new generic compiler/discovery/config adapter; new v2
artifact issuer; checked-entry codecs and persistent Project runner; source-bound
compact startup evidence admission plus module/action ledger. Reuse rather than
fork the process monitor/cache primitives, but preserve fixed v1 behavior and
its historical receipts. Land only after genuine entropy/startup support exists;
otherwise land the compiler/prepare metadata slice explicitly without claiming
ordinary-project execution readiness.

Acceptance corpus (source unchanged during each build):

1. Existing three-file FP Lean greeting: ordinary implicit Init, complete startup,
   native stdout bytes, default Loader cold/hit, repeated main with no reseed.
2. Three local arithmetic modules with an earlier-definition import/diamond;
   Nat→Nat calls at0,42,Long.MAX_VALUE,2^64,2^200, exact native comparison.
3. Two-module String identity/append fixture with NUL, λ, emoji and combining
   characters; exact UTF-8 result, surrogate rejection before guest effects.
4. A Nat→Nat fixture using internal List construction/fold and recursion; no
   public List codec or reduced source-body recognizer.
5. Theorem-only imported module plus callable definitions: native proof checking,
   no assertion of JavaTC/CI-store hydration.
6. Negative cycle/external dependency/module header, wrong signature, unsafe/
   polymorphic/extern entry, unknown native ABI, anonymous/builtin startup,
   mutated cache, interrupted build, close-vs-wait and startup failure. Verify
   zero entry execution, no init replay and retained real journals as appropriate.

For each positive case separately measure cold compile, validated cache hit,
Project startup and repeated calls. Repeated calls must perform zero native
processes and no Program/source reload. Validate exact result bytes/types,
initialized-global identity/no second entropy read, normal lifetime close and
failure/cancellation custody. Jar-only/offline precompiled-artifact deployment
and a public Java facade are later explicit gates, not consequences of this plan.
