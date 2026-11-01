# Compact native startup evidence proposal

This is source-only research. No accepted helper, binary, compiler, runtime or
landing source was changed; no native/JVM process was launched. The Python audits
read one bounded metadata module/CAS row at a time. This profile concerns the
original interpreter's initialization attributes, not eager native-C value
initialization, full ModuleData/kernel imports or general builtin bootstrapping.

## Concrete first gate

Produce one compact, authenticated startup bundle for ordinary legacy `Init`
imports, register all canonical Headers/bodies, then run its one actual regular
named initializer through the separately reviewed `startInitializer(global,
action)` runtime transaction. This should establish only the initialization
requirements selected by this interpreter profile. It does not establish all
native-C startup side effects, arbitrary imported native libraries or hosted Init.

The saved metadata census is exact:

- Metadata SHA256: 757057e2962068afb48641ad5cb3fe25af46f8ece8be1c48c634a619c8ac0f2c.
- 631 ordered modules, 3155 physical parts, no builtin attribute observations.
- Module index511 is Init.Data.Random. Its regular pair occurs in root2557
  (Random.olean.private) and root2559 (Random.ir). The pair is identical.
- Target global is the actual typed Name IO.stdGenRef. Its original IR row SHA
  is 97976b01a87c3fc473bbf5408c47b79625a168239d660659f63770f3b1b5068f:
  zero parameters, result tobject, runtime role initialized, actual body
  unreachable. The producer must preserve this row, not replace it with a body
  returning a fabricated reference.
- The actual private action Name is stored verbatim in census.json; do not
  reconstruct its display string or numeric hygiene leaves. Original action row
  SHA526bcf3a5d70f4d1ec594fe7bab187be148466c44e4ca173d1739bf04723bb30
  has exactly one owned void parameter and object result.
- Complete static closure of action plus target:60 rows, including26 extern
  rows. This includes error/panic branches and closed constants; do not prune
  them merely because an eight-byte successful entropy response normally avoids
  them. closure-census.json records every actual typed Name, original row hash,
  ABI, dependency and role without copying the full original bodies.
- These row facts were obtained by positional lookup in the already authenticated
  catalogue (source index74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e,
  datae7d2aadb70d7f3f4157a952ea05d5b4f857831607f8453a24dc692ed4be4acec)
  and hash-checked bounded CAS reads, independently of a native initializer run.

## Original semantics to retain

Pinned source is Lean819816b2e0a3bf405af45ae5c7af2491d8f5bee6:

- Compiler/InitAttr.lean50–83: ordered ParametricAttribute entries. Regular
  non-meta initialization is preserved in IR; .olean/private and IR can overlap.
- InitAttr.lean112–141: getInitFnNameFor? deliberately returns none for an
  anonymous IO Unit action. isIOUnitInitFn includes both regular and builtin
  anonymous actions. Therefore inventories must preserve the actual (decl,init)
  tuples, not enumerate only successful getInitFnNameFor? calls.
- InitAttr.lean162–209: walk actual env.header.modules order. Native module
  initializer availability may short-circuit interpreter fallback. If no native
  initializer exists, run regular entries in declaration order, append IR entries
  not already in module entries, skip runtime declarations only when initRuntime
  is false. initRuntime is Elab.inServer || effective irPhases != runtime.
  Track at-most-once by actual module identity. Preserve the first list as-is;
  the source filters duplicates only while appending the IR list.
- A pair (decl,anonymous) evaluates decl as IO Unit without writing a target
  global. A pair (decl,initDecl) calls initDecl and installs the IO.ok payload as
  decl's global value. ir_interpreter.cpp1127–1149 calls the original boxed
  resolver, marks the payload persistent, and updates native storage or the
  interpreter global table; IO.error is returned without publishing the global.
- The interpreter does NOT append builtinInitAttr entries to this regular loop.
  Builtin initialization is a distinct native/bootstrap obligation (see also
  runInitAttrsForModules documentation about already initialized builtin effects).
  Exposing a builtin inventory is required; replaying every builtin as an
  ordinary regular action would change the profile.
- Original closed/ground/value memoization is independent of this action order.
  LCNF/EmitC.lean emits native startup for ordinary constants as well; do not
  relabel that eager native policy as interpreter initialization parity.

## Producer API and format

Prefer a NEW NativeStartupEvidence executable/namespace, or an explicitly opt-in
mode after review. Do not modify NativeEntryEvidence entry admission to permit
initializer roots. Reuse its bounded original IR serializer/raw and boxed lookup
logic through a reviewed shared module or a small isolated initial copy; the
accepted entry helper remains pinned while this producer is validated.

`--startup REQUEST.json` accepts an exact typed requested-module/import list,
legacy/module mode and declared interpreter init profile. They are requests, not
caller proofs. The producer imports those actual modules under the configured
trusted toolchain, obtains actual ordered EffectiveImports/header mode/options,
and emits lean-native-startup-evidence/1 containing:

1. Compiler/tool/target/producer pins; actual typed requested imports, effective
   ordered imports, import phases, global level, module mode and inServer option.
   Native-import initialization can itself execute native/interpreted effects;
   record that native build boundary honestly. Do not claim metadata-only native
   import unless a separate side-effect-free original API is proven.
2. For each module, exact regular and builtin module-entry arrays plus IR-entry
   arrays, retaining order, duplicates and anonymous Names. Also emit the exact
   regular deduplicated sequence and phase decision selected by source rules.
   Keep source lists and selected actions separate so consumers can recompute.
3. Every selected action has kind named-global or anonymous-io-unit, original
   category, actual module/order/tuple provenance and exact typed action/global
   Names. Capture actual native CI type/kind/universe evidence. Named actions
   require native DefEq IO(target CI type); anonymous actions require IO Unit.
   Neither a raw ABI nor source syntax alone establishes that type relationship.
4. Preserve actual raw and original interpreter-selected boxed callable Names/
   ABIs. Preserve the returned selected declaration itself (the base-module-index
   lookup matters for private/generated bridges). The current named runtime seam
   supports raw owned void→object only; a producer must report unsupported
   callable ABI rather than coerce an arbitrary action into that seam.
5. Export complete original action/target static IR closure and redirects/roles,
   all typed dependencies and dynamic AP sites. Reserve every Header before any
   body is materialized. Missing bodies or capabilities are explicit refusal.
   No suffix-based action discovery, code rewriting or manufactured empty state.
6. Builtin arrays/actions remain explicitly categorized. The first Init profile
   requires their arrays empty. A future profile must bind actual native builtin
   effects to reviewed JVM replacements or a genuine source bootstrap before
   marking those modules ready; never quietly omit or run them as regular init.

Bounds: at most4096 ordered modules,16384 raw attribute occurrences,2048 closure
rows,32768 queued dependencies, bounded type/IR trees and16MiB output. Capture
full bundle/source/tool/input/output digests in the native build receipt; consume
only an actual trusted build receipt or independently authenticated artifact.
Caller maps/ready flags/type tags are not authority.

## Missing capabilities and first runtime admission

The actual entropy row is IO.getRandomBytes, SHA
afc15888b42a236a70bd422ced2bacca2d0808810d0ee7540495985d7ff9c368:
owned usize, owned void→object, extern lean_io_get_random_bytes. It must return
actual IO.ok ByteArray or IO.error, not BaseIO ByteArray or a fake seeded global.
Init/Data/Random.lean141–143 requests exactly8 bytes, interprets them UInt64 LE,
converts to Nat, runs mkStdGen and creates the reference with ST.Prim.mkRef.
The source runtime io.cpp863–928 uses OS entropy, returns an empty ByteArray for
zero, bounds allocation and reports actual OS errors. A bounded JVM OS-entropy
provider/native implementation needs an explicit allocation cap, exact unsigned
USize admission, real initialized ByteArray logical size/capacity, and honest IO
error behavior. Tests may inject explicit deterministic entropy as a labelled test
capability; that is not default native entropy parity.

The other missing symbol in current Java source is lean_byte_array_get, original
ByteArray.get! row4ed4c7387fe8561b580ae83628252560821401449046852e4156a2bcaf259360:
borrowed object, borrowed tobject→uint8. lean.h1182–1190 returns0 for out-of-range
or MPZ Nat indices; it does not implement unchecked uget semantics. The complete
closure includes this fallback path even though successful8-byte entropy should
keep accesses valid. The other24 extern rows' symbols are present; exact ABI
validation against the actual runtime remains mandatory (source presence alone
is not a runtime ABI proof).

### Narrow runtime changes to review separately

ByteArray.get! should be a small borrowed intrinsic, not a generic checked-index
helper that throws or invokes Lean panic. Reuse actual byteArray(value) realm/
kind/live-size validation and exact Nat admission. Compare the nonnegative Nat
against logical size as a BigInteger (or compare before narrowing); return unsigned
byte0..255 when in bounds, otherwise0, including MPZ indices. Never truncate a
huge Nat, inspect capacity instead of size, decrement either borrowed argument,
or reuse lean_byte_array_fget/unchecked-uget semantics. Invalid host carriers or
malformed Nodes are API/profile failures, distinct from valid out-of-range Nat.

Entropy cannot return an ordinary Java byte[] as a guest ByteArray. The current
Engine ByteArrayState and newByteArray are private; no supported public factory
exists. ImportGraph is an inappropriate per-host-result allocation protocol.
Two coherent choices exist; prefer the first for the tiny supported native symbol:

- Add a bounded engine entropy intrinsic/capability that alone uses newByteArray,
  fills its private storage, and returns an actual IO envelope. Configure its OS
  source once before use; default source must be real entropy. A separate explicit
  deterministic source is allowed only for labelled tests. This keeps Node
  representation, allocation accounting and ownership in the engine.
- If entropy remains host-serviced, add a narrow typed completion such as
  completeEntropyBytes(actualRequest, hostToken, byte[]) (illustrative name),
  which validates the exact actual pending request/Header/ABI/engine/thread,
  preflights size/result ownership, copies the host bytes into one newly owned
  engine ByteArray, constructs IO.ok and commits the same resume token once.
  Do not expose arbitrary metadata/tag construction or accept an accepted flag.
  An error-completion form needs a separately reviewed actual IO.Error codec.

Both choices must preflight actual USize lane and unsigned bounds before any
entropy effect or guest allocation; a negative Java long can represent a huge
unsigned USize and must not become a negative/short allocation. Copy host arrays;
caller mutation must not alter issued ByteArray content. Preallocate/publish an
effect journal before the read, distinguish pre-effect rejection from post-read
completion failure, retain the owned output on a failed commit, and never repeat
the entropy read automatically. Close the actual OS resource in every outcome;
if a callback owns it, failed completion cannot silently drop its handle.

An actual IO error requires EST.Out.error carrying an actual IO.Error value,
not a raw String, HostException, BaseIO value or successful empty buffer. The
pinned IO.Error constructors include OS code/details and sometimes filename;
decode_io_error uses those real variants. Java IOException alone does not expose
portable POSIX errno, and SecureRandom's default algorithm is not a promise of
the same Linux /dev/urandom source. The implementation must choose and document
its error/source profile: for exact Linux correspondence use a reviewed
OS-error/errno adapter, or admit an explicitly narrower portable IO.Error mapping
with truthful code/details. Profile size-cap rejection is not evidence that the
OS returned ENOMEM. First success-only probes may stop and preserve a failed
host packet on actual source errors, but that is not a release-ready IO error
implementation. Validate actual result constructors with source-backed evidence
or a reviewed engine codec, never by guessing a tag from the result name.

Runtime tests should include ByteArray.get! at0,size-1,size,huge Nat and unused
capacity; borrowing/RC, foreign/dead Nodes, alias preservation, entropy sizes0/8
and unsigned over-cap, short/error reads, copied-array mutation, wrong request/
Header/engine and duplicate completion. Deterministic bytes00..07 yield little-
endian seed506097522914230528 and source mkStdGen state (990732983,235670034)
(these expected numbers were calculated from source, not measured by a guest).
Execute the actual private action, check IO.ok's genuine Ref/StdGen payload,
publish IO.stdGenRef, release the result wrapper, and show repeated global reads
return that same reference without another entropy action. Then run the real
default source separately and check shape/valid ranges, not reproducible random
bytes. The whole ordered module plan needs an at-most-once ledger whose pending/
done/failed states survive pauses and whose failure prevents Project readiness.

The runtime sequence is configure capabilities→canonical Headers→all bodies→one
named initializer transaction→take IO result→validate successful global binding→
mark module/profile ready. IO.error, pause, budget or ownership failure preserves
the actual pending transaction; no entry executes and no automatic retry/reseed
occurs. Anonymous actions need a separate at-most-once module/action ledger and
IO Unit result contract; never forge a dummy global merely to reuse the named
initializer API. Project readiness must cover the whole selected ordered plan,
while normal value-cache ownership and teardown stay independently journaled.

## Proposed review/probe order

1. Approve this format/profile and the distinction between regular fallback,
   anonymous actions and native builtin obligations.
2. Implement an isolated producer; native fixtures cover named/anonymous regular
   and builtin attrs, module/IR duplicate pairs, phase filtering and exact private
   callable selection. Export Init's compact plan/closure under native bounds.
3. Add exact ByteArray.get! and entropy capability semantics/tests separately.
4. Authenticate the compact output and execute the genuine random action on an
   explicit JVM engine, validate global reuse/no second entropy action and normal
   teardown. Compare source results with explicit deterministic bytes for tests;
   keep real entropy nondeterminism and native/JVM runtime boundaries visible.
5. Only then integrate plan readiness with generic project entry execution. This
   does not require materializing11M ModuleData objects or a full kernel store.
