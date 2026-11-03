# Lean/JVM compatibility ledger

This ledger describes the experimental bounded SDK and the Campaign 2 candidate,
not unrestricted Lean compatibility. It is documentation, not an admission list
or runtime certificate. The executable public authority is
[capabilities.clj](src/ansatz/lean/jvm/capabilities.clj), checked against actual
extern ABIs and the prepared Program. Internal engine implementation, public
admission, host conversion, source preparation and platform policy are separate
questions. Passing one does not establish the others.

The cohort is official Lean **4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Linux x86-64 with 64-bit words,
and JDK 17 or later. Upstream obligations include
[compiler IR](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Compiler/IR/Basic.lean),
[runtime objects](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp),
[native IO](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/io.cpp)
and [Lean stream definitions](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/System/IO.lean).
These are sources for semantic review, not evidence that all their operations
have been ported. There is no aggregate compatibility percentage.

## Status and evidence

“Current profile” means the existing bounded contract documented in the
[SDK guide](README.md); consult release receipts for any published artifact.
The proof-backed sort/sharing work shipped in **0.2.583** through
[PR #374](https://github.com/replikativ/ansatz/pull/374).
Finite stdio landed through [PR #375](https://github.com/replikativ/ansatz/pull/375);
runtime-domain/monad/error work through [PR #376](https://github.com/replikativ/ansatz/pull/376),
and explicit installed imports through [PR #377](https://github.com/replikativ/ansatz/pull/377).
The new v3 datatype boundary and opt-in filesystem slice described below are
integration boundaries; the v3 producer archive is published separately. Their
local receipts do not establish a published release. “Unreviewed” means no complete semantic-family audit,
even when some symbols have engine implementations.

[Historical validation](validation.json) preserves its original scope. The
[sort example](examples/fp-lean-sort/README.md) records the unchanged source pin
and explicit adapters. New candidates require their own exact-JAR receipts under
the [release checks](RELEASE_CHECKLIST.md). Synthetic models below exercise real
engine operations or admission rules but are not native execution receipts.

## Reviewed boundaries by layer

The [host bindings](FFI.md) add Java/Clojure implementations for explicit
pure or synchronous IO imports and noinline reference replacements. They use the
existing first-order value boundary and type-driven constructor factories. The
[reference corpus](examples/pure-ffi/README.md) compares native, JVM-reference and
host execution, including initialization and the audited String.any worker. The
[foreign-import corpus](examples/foreign-ffi/README.md) covers required bodyless
imports and explicit catchable IO errors. The matching [producer](producer/candidate-v4.json) is published and public-download verified. Function-valued callbacks, async work and
opaque host resource handles remain outside this profile.

| Layer / obligation | Status and boundary | Source / checks / remaining evidence |
| --- | --- | --- |
| Preparation: local source graph | Default: one root and a closed acyclic local import DAG plus installed Init; legacy private/ordinary source headers. Explicit finite installed-import lists add exact sysroot modules, with compiled-product identity and actual effective-graph checks. Native elaboration is trusted-source execution and can run metaprograms or compile-time IO. | [Producer guide](producer/README.md), [preparation](PREPARATION.md), [compiler sources](src/ansatz/lean/jvm/compiler), [source acceptance](test/source_acceptance.clj). This permits no extra externs or initialization forms. General package resolution and modern local module transport remain separate. The [persistent-map example](examples/persistent-map/README.md) passes independent native, public source/cache and artifact checks in the integration candidate; this is not a published-release claim. |
| Preparation: built Lake workspace | Candidate: explicit `builtLakeWorkspace()` consumes an already resolved and built workspace, including path/Git dependencies and modern compiled module products. Up-to-date checks issue no build/update; exact workspace products are captured unchanged. | [Lake scope and assessment](LAKE.md), [native acceptance](test/lake_acceptance.clj), [offline models](test/lake_workspace_checks.clj). Non-Init closure limit: 128 modules. Dependency resolution/build orchestration and arbitrary runtime coverage remain outside this mode. |
| Preparation: selected entries | Current profile: explicitly selected top-level, closed monomorphic functions, pure or IO, 0–64 explicit arguments; current producer selects 1–1,024 entries. Older producer cohorts can have a smaller entry limit. | [Signature rules](src/ansatz/lean/jvm/signature.clj), [entry evidence](src/ansatz/lean/jvm/entry.clj), [native entry producer](../../tools/lean-producer/src/NativeGeneralEntryEvidence.lean), [entry checks](test/entry_checks.clj). Polymorphic, dependent, implicit/proof-bearing or higher-order host arguments need a new entry contract or explicit monomorphic adapters. |
| Deployment: prepared artifacts | Current profile: authenticated bounded artifacts run without native Lean, javac, Python or a source checkout. Native preparation and JVM execution remain independent. | [Artifact loader](src/ansatz/lean/jvm/artifact.clj), [consumer checks](consumer/README.md), [artifact models](test/ansatz_lean_jvm_artifact_models.clj). Artifact execution does not independently kernel-check imported theorems. |
| Engine: ordinary compiler IR | Internal implementation includes constructors and scalar fields, projections, direct/partial/closure calls, joins, mutation, ownership instructions, cases and returns. This is not a completed audit of every pinned IR form. | [Interpreter](src-java/ansatz/lean/jvm/internal/exec/Interpreter.java), [engine contracts](test-engine/README.md), [typed exporter](../../tools/lean-producer/src/TypedSourceExport.lean). `metadataType` rejects structured struct/union type encodings; extending metadata alone would not implement their execution semantics. |
| Engine: wide scalar cases | Reviewed implementation caveat, not a demonstrated failure of all wide-word programs: alternative tags use Java `int`, while `caseTag` can produce `long`; `-1` also denotes default. Full-width scalar alternative encoding/dispatch needs a native-backed audit before broad claims. | Interpreter `body`, `caseTag` and both CASE drivers. Ordinary compiler-generated constructor cases and tested scalar programs do not establish arbitrary UInt64/USize case coverage. |
| Public runtime admission | Current profile is task-free, with explicit audited arithmetic, strings, arrays/bytes, references and other families in the capability table. Unknown required externs or mismatched ABIs fail before startup; an internal registry entry alone is insufficient. | [Capabilities](src/ansatz/lean/jvm/capabilities.clj), [startup publication](src/ansatz/lean/jvm/startup.clj), [capability models](test/ansatz_lean_jvm_capability_models.clj). Public profile restrictions can be narrower than engine implementations. |
| Host values: common types | Current profile: Nat/Int, Bool, String, Unit, fixed-width integers, USize/ISize, Float/Float32, Char, Prod, Option, List, Array, ByteArray, Sum and Except, nested within conversion budgets. Results are host values and copies, not raw guest Nodes. | [Carrier table](README.md#values-resources-and-lifetime), [value examples](VALUE_EXAMPLES.md), [signature](src/ansatz/lean/jvm/signature.clj), [argument planner](src/ansatz/lean/jvm/argument.clj), [value decoder](src/ansatz/lean/jvm/value.clj), [value checks](test/ansatz_lean_jvm_value_checks.clj). V1/v2 carriers and byte copies remain unchanged; v3 typed carriers follow the separate row below. |
| Host values: nominal/custom data | New v3 source/artifact boundary: closed proof-free enums, records, ordinary recursive datatypes and finite monomorphic generic instances. Native-derived `LeanType` metadata, immutable `LeanData`/`LeanBytes` and Clojure tagged map/indexed views support compatible detached reuse and explicit materialization. Uses the separate published v3 producer; no v1/v2 retrofit. | [Datatype contract](DATATYPE_INTEROP_PLAN.md), [value examples](VALUE_EXAMPLES.md#automatic-datatype-values-v3), [independent expression application](examples/datatypes/README.md), [native regression captures](test/fixtures/nominal-entry-v3/README.md). Public Java/Clojure source and native-free artifact calls match native fingerprints for four oracle datatypes; the independent three-file expression application exercises evaluation, transformation, records and IO. Indexed/dependent, proof-bearing, mutual/nonuniform recursion, function/resource fields and cyclic values remain refused. Cross-Project reuse requires matching logical, origin-product, representation and runtime-class identities. |
| Sharing diagnostics | Introduced in 0.2.583; this candidate replaces mandatory static shape admission with actual runtime domain checks. `lean_dbg_trace_if_shared` keeps its owning supported result unchanged and captures native-style stderr for non-scalar, non-exclusive managed objects. | [Engine checks](test-java/SharingTraceChecks.java), [source checks](test/source_acceptance.clj), [sort example](examples/fp-lean-sort/README.md). String/BigInteger leaves lack logical RC and throw if reached. Earlier guest work may occur; a failed Project is terminal. Projections and closures are not themselves a reason to reject a known primitive. Source types never establish heap-leaf ownership, including unsafe implementation replacements. All source/artifact/full-ABI checks remain. C-string NUL truncation and allocation-dependent trace counts remain observable. Pure checked calls still reject captured output. |
| Invocation stdio | Finite supplied stdin and independent raw stdout/stderr capture; no process-global stdin takeover. Existing simple calls use empty input. Getter admission includes stdin/stderr alongside stdout. | [Invocation options](src-java/ansatz/lean/jvm/InvocationOptions.java), [project lifecycle](src/ansatz/lean/jvm/project.clj), [captured-stream checks](test-java/CapturedStdioChecks.java), [options checks](test-java/InvocationOptionsChecks.java). Unchanged HelloName, EarlyReturn and ForMIO pass native differential checks, including EOF, CRLF and NUL. [StdIOSmoke](consumer/StdIOSmoke.java) passes Java/Clojure calls from an application JAR without the native frontend. Candidate sort-CLI coverage follows the runtime-domain contract above. |
| Monad composition and guest errors | Ordinary monad implementations execute as IR. The candidate adds a native-backed ReaderT/StateT/ExceptT/ST/EST/StateRefT corpus and partial uncaught `userError` details; other IO.Error variants remain generic. | [Monad corpus](examples/monad-conformance/README.md), [acceptance helpers](test/monad_acceptance.clj), [error models](test/io_error_checks.clj). Java/Clojure `LeanException.details()` returns immutable bounded kind/message fields for the independently witnessed userError layout. This adds neither arbitrary EIO host signatures nor custom datatype codecs. Host limits/cancellation do not promise guest finally execution. |
| Filesystem | Integration candidate: explicit read-only or writable Linux regular-file context, all five open modes, byte/text writes, flush, rewind, truncate and bounded metadata. Read-only configurations remain read-only; default runtime scopes supply no filesystem permission. | [Filesystem contract](FILESYSTEM.md), unchanged two-file [Feline](examples/fp-lean-feline/README.md), authored [writer](examples/filesystem-writing/README.md) and [append oracle](examples/filesystem-append-cursor/README.md). Public source/cache/artifact and isolated Java/Clojure consumers pass; write-through parity is checked at synchronization boundaries. Directory operations, special-file opens, symlinks, absolute/parent paths, filesystem initializers and forks remain unsupported. Policy failures are distinct from guest IO errors; external writes are not rolled back. |
| Tasks and forks | Internal partial implementations and engine contracts exist; the public Project profile enables neither task runtime nor public forks. | [Engine contracts](test-engine/README.md), [capabilities](src/ansatz/lean/jvm/capabilities.clj). C2's internal eager-fork test copies the input cursor/epoch and captures while sharing only private immutable input bytes. That is not a public fork API or an OS-resource snapshot policy. |
| Platform and resources | Deliberate bounded policy: admitted Linux/64-bit cohort, cooperative two-million-instruction/five-second calls, bounded conversion/allocation/output and explicit failure. These are not hard JVM memory or preemption guarantees. | [Project budgets](src/ansatz/lean/jvm/project.clj), [scalar/buffer rules](src/ansatz/lean/jvm/scalar_buffer.clj), [resource checks](test-java/RuntimeResourceChecks.java), [SDK limits](README.md#values-resources-and-lifetime). A stopped failed Project is not replayed; retirement may abandon independently checked pure heap for JVM GC, without claiming guest finalizers or rollback. |

## Supplied-stdio contract

- Input is an immutable private snapshot, at most **1 MiB** per invocation.
  Java text input must be valid Unicode and encode within that bound; byte input
  can contain arbitrary octets. Each invocation starts at cursor zero; EOF stays
  empty for that finite input. Byte reads and line reads share one cursor.
- `getLine` includes LF, preserves CR and embedded NUL, and uses the pinned
  native Lean lossy UTF-8 recovery rule. Read allocation, decoding and cancellation
  checks precede committing the cursor. This models native Handle-like input,
  not `Stream.ofBuffer`'s distinct NUL/invalid-UTF-8 behavior.
- Output bytes are canonical. `IOResult.stdoutBytes()` and `stderrBytes()` return
  defensive copies. Host text views use Java UTF-8 replacement decoding; they
  are intentionally distinct from native Lean's invalid-sequence grouping on
  stdin. Writing arbitrary malformed bytes does not promise identical replacement
  text between those decoders. Valid UTF-8, including NUL, is preserved.
- Each output channel defaults to **16 MiB** and can be tightened independently.
  Pending initialization bytes count toward the first IO result and its limits;
  that prefix is reserved before entering the call. Over-budget writes fail
  before capture mutation. These limits do not describe process stderr/stdout.
- Wrong-direction operations and stale escaped stream methods return
  `IO.Error.userError` (tag 18) through IO. Stale `isTty` is a terminal boundary
  because BaseIO has no IO.Error result; current streams report false.
  Epochs prevent old streams from consuming a later invocation's input or output.
- Stdio setters/redirection remain publicly unsupported. The separate internal
  original `Stream.ofBuffer`/`stdioContext` profile cannot overlap an invocation
  context. Arbitrary host streams, files, sockets and processes are not supplied
  by `InvocationOptions`.

## Upstream obligations still requiring family review

These are work items, not a claim that every operation is absent. Review actual
source, full ABI, representation domains, ownership, effects, errors and limits
before promoting any family into public admission.

| Family | Known scope / next evidence |
| --- | --- |
| Numeric, string, array/byte, reference and compiler primitives | Existing implementations/tests cover selected domains. Reconcile compiler-selected primitives and edge cases against pinned native sources; a lexical extern count is insufficient. |
| Debug/panic and ownership-sensitive observations | Actual-value guards cover the supported sharing domain. Generic heap-leaf RC, panic default-return semantics, thunks/finalizers and other observations need separate audit; the current panic path is a declared terminal trap. |
| Clock, environment and process services | No broad public family contract. Review determinism, platform behavior, handles, cancellation and errors before admission. |
| Randomness | Existing initialization uses an explicit JDK entropy capability and retained Project state. This does not establish every upstream random/entropy service or native-provider equivalence; see [startup](src/ansatz/lean/jvm/startup.clj) and [project](src/ansatz/lean/jvm/project.clj). |
| Scheduler/tasks, synchronization and external resources | Partial internal workers do not establish upstream scheduling semantics or safe public resource lifetimes/forks. OS handles cannot be duplicated by copying guest memory. |
| Package/module preparation | Add pinned dependency-aware resolution, initialization and cache validation for selected unchanged projects. Merely allowing Std/Lean/Lake import names is insufficient. |
| Arbitrary native FFI | Not implemented as a generic facility. Package-defined externs need explicit Java implementations or a separately designed optional native bridge; exact symbol/ABI validation remains mandatory. |
| Official frontend/compiler hosting | Future milestone: complete parser, elaborator/tactic, import/export and compiler workloads, including Name/Level/Expr, environment, serialization and native services. Loading exporter helpers or isolated internal workers is not self-hosting. |
| Ansatz kernel/DSL exchange | Future separate integration: type/name translation, theorem/declaration transfer and an explicit checking policy. Native frontend elaboration and JVM execution do not import proofs into the core Ansatz kernel. |

For each extension, record source/entry/admission/execution stage separately,
retain unchanged sources and explicit adapters, and compare native references
with the exact candidate JVM artifact. Preserve expected refusals alongside
successful cases. The filesystem/Feline candidate adds a separate owned-resource
profile; broader datatype families, typed callbacks and package preparation
remain distinct follow-up work.
