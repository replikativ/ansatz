# Private delayed-instantiation foundation

Stage four supplies the generation cache, pending resolvability analysis and
scoped substitution maintenance for a future complete delayed Expr pass. The
original `lean_instantiate_expr_mvars` remains unavailable. The complete delayed
transform, two-pass root lifetime integration and public/native admission remain
separate stages. This unit introduces private fixed research protocols, rather
than a public guest invocation or world-authority API.

Source is Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, principally
`src/library/scope_cache.h` and the `instantiate_delayed_fn` portion of
`src/library/instantiate_mvars.cpp`. It reuses the nineteen canonical helper
roles and original finite fixture from the
[direct pass](JAVA_EXPR_DIRECT_PASS.md), plus the existing typed
[replacement/lift/beta jobs](JAVA_EXPR_MACHINERY.md). Every helper retains exact
bodyless metadata/Name/raw ABI/borrow/source/current Function validation. The
trusted loader authenticates source bytes; matching descriptive Header hashes
alone are not authentication. Missing ordinary bodies use CodeRequest.

## Generation cache

The cache maps each borrowed `(Expr identity, binderDepth)` to a stack of owning
entries. An entry stores its result credit, current valid level, immutable
scope-generation snapshot and result-scope watermark. Push links a fresh
immutable generation node and advances scope; pop follows its parent. Entry
maintenance occurs lazily. Scope and binder depth advance independently.

Rewind evicts results depending on popped scopes, degrades valid levels, compares
generation chains and searches matching ancestors. A surviving lower valid level
still misses at the current scope. Lookup propagates its result-scope watermark.
Insert preserves an existing pointer when the surviving top has the same result
scope, even after traversal computed a fresh value. It then replaces the covered
entry interval. A single last-value map, cache clearing on pop or a depth-only
cache would change those sharing choices.

Each eviction moves the entry to explicit retiring escrow before removing its
stack slot. Its resource reservation survives until the real release completes.
The insert operation separately tracks computed caller result, local shared copy,
old-value replacement copy and returned copy. It retains replacements before
releasing old values. Lookup tracks its optional and returned-copy occurrences.
Failures retain the exact unfinished owner/disposition packet.

Cache keys are bounded per `(Expr,depth)` bucket, including empty stacks retained
after eviction. Live entries and cumulative generation allocations have separate
limits. Raw indexes and bucket keys detach while input anchors still live. Seal
performs bounded raw-index clears and bucket-key clearing in one Java step; this
bounded maintenance tail is not a per-entry resumable or hard wall-time promise.
Owned eviction/member releases are resumable. All generations contain only final
primitive/parent fields and no guest references; fork may share those chains.

## Resolvability

A semantic Name map stores pending IN_PROGRESS/YES/NO states. It owns its Name
keys; a repeated IN_PROGRESS pending value is false. Original getters provide
assignment Options. The Option and separate full-expression Expr temporary stay
owned through analysis. The temporary retires before the YES/NO update, while the
Option remains until that pending frame returns. Analysis does no context setter
writeback and preserves its pending cache across the whole session.

Expression-mvar-free values return true regardless of universe mvars. Expression
Boolean cache lookup samples `!exclusive` on entry; storage samples it again on
exit. The Boolean cache owns no Expr keys or values. Input/context anchors keep those borrowed keys valid without added key retains.
The future two-pass caller must also preserve its reviewed saved assignment owners. Bare expression MVars are false. Structural Apps check function then
argument, binders domain then body, lets type/value/body, and mdata/proj their
child. MVar-headed Apps require delayed assignment, enough arguments, a resolvable
pending value and every argument, visited outermost first.

The delayed fvars accessor runs before arity checking and pending-name access.
Each accessor receives its own retained argument in addition to the separate
by-value delayed-record temporary required by `option_ref::get_val()`. Returned
Options, arrays, Names and raw receiver slots each have explicit ownership.
Malformed replies remain in their owning receiver; they do not become a normal
false result or trigger helper replay.

## Substitution and restoration

The semantic Name table owns independent key/value credits with recorded binder
depth and generation scope. Installation saves a separate Name and any old value,
then copies its new argument before releasing a replaced value. Production
installation may alias an enclosing buffer's credit records; those aliases are
not additional owners. The research setup deliberately owns its argument copies
and records that distinction in the maintenance frame.

Pop clamps the result-scope watermark before restoration. Saved entries restore
in literal FORWARD array order. Duplicate fvar Names are supported with that
low-level behavior: an initially absent duplicate can remain mapped after the
loop. No restored-map-empty assertion is added, and a watermark above current
scope is accepted; native rewind evicts that entry when next accessed. Zero
fvars still create a generation scope while the substitution stays empty. Outer
mode is determined by map emptiness.

Restoration finishes before saved-record/buffer destruction. Saved old values
retire before their Name keys, and erased map values before their keys. Separate
maintenance stages preserve every intermediate owner through releases. A lookup
copies its optional/result in source order and applies the existing lift worker
when binder depth increases. That nested worker borrows its map-backed input,
uses no synthetic root retain, shares the caller's budget and does not reset root
execution counters. The native replacement `rc != 1` heuristic remains unchanged.

## Fixed research protocols and lifecycle

Private action17 accepts cloned data-only command records. Cache commands are
push, pop, lookup and insert over owned anchor indices. Resolver commands analyze
one anchored Expr. Substitution commands install an anchored fvars/argument Array,
restore a saved frame and look up a Name at a checked binder depth. Commands
cannot supply guest Functions, callback capabilities, bodies or source authority.
The engine must be open, idle and active explicit; complete helper policy,
commands, extents, known owned aliases and bounded preflight scans are checked
before ownership publication.

The research caller owns its explicit anchors. Production sessions borrow their
already anchored traversal inputs. The private report is an ordinary ctor0
`[context,lastOwnedResultOr0,lastPrimitiveObservation]`, not an original Lean ABI.
Observation logs contain primitive numbers only. Before report publication the
protocol seals raw indexes, retires anchors and drains pending Names, cache
results and remaining substitution owners. No successful failed-engine unwind or
arbitrary native finalizer-order equivalence is claimed.

One MVarContextCell and InstantiationBudget are shared by sessions and nested
workers. Helper entry commits match the actual current action, Function and
original packet array at frame/Code publication before tick. Substitution,
lookup, resolver and cache stages have one current operation and no reentrant
public start. Same-memo fork remaps all mutable frames, Nodes, credits, maps,
packets, reservations, receiver aliases, context and budget. No Node field or
runtime source-ID memo is added.

All work limits are host profile guards, not native heartbeats or a global heap
cap. Interruption is cooperative. Input shape/cache-word checks are not nominal
AST certification or a whole-graph validation pass. Labeled malformed storage and
helper-body tests remain protocol models.

## Validation status

Astra reviewed complete source
`32dd9d35f88d0e2238de580cff83620cda056d7e23be8b4a203365d921e532c3`
before private activation and found no source blocker. Activation changes only
the private READY flag, yielding source
`03c96892ab58c4a7ad2eed6c19a61178d2cdf359e4db4df48488bc75902718cf`.
Bounded Java11 compilation with 256 MiB produced immutable jar
`e737dc84ed4c4fe7c13993326a4c14f6df7a8cb69fed135a1ab21180244737f6`.
The author launches no JVM test runner, native executable or full image.

The independent test oracle models a conceptual stack of scope maps with integer
value tokens; it does not repeat the runtime generation-linked per-key stacks.
Additional focused tests use original helpers with explicitly labeled context
storage/body adapters. Parent runtime observations and combined-gate results will
be recorded separately when available. Complete pass two/native/frontend support
is not established by these private foundation tests.

The parent retained 384 MiB JVM passed **10 semantic tests / 211 assertions** and
**8 control tests / 129 assertions**, zero failures/errors, on that unchanged
source/jar. Semantic file SHA is
`a719ee70069ff445673b19dc9bed8b37e1d6c8083e397481a6df76adacdb204a`;
final control file SHA is
`ed85b6baf03dc36a3cbe5f1cc02ebf65802b4cce87094d4bed05d8aae61449de`.
Parent receipts under `target/java-expr-direct-integration-v1/`:

- `delayed-semantic-v1.out`:
  `7ddec13594593de3c7bcf475dc63a240cd462bdc1886c066c97bea930447e1c9`.
- `delayed-control-v2.out`:
  `30e2e1f484178afa2204bd5aaddd1c1b3cfcdd7fa218a467146d23a83b57086b`.

The first member-drain model expected a pure Task callback after the containing
zero-shell batch had already removed its final owner. LIFO destruction correctly
retired/unlinked that dependent before Promise destruction, so the callback was
not required. The corrected fixture retains an independent Task occurrence as
the CACHE protocol's opaque context until report retirement. Its Promise drop
then genuinely demands finalizer Code, Host reply and fork while the cache
reservation remains held. This is explicitly nonnominal storage/opaque-context
control evidence, not an original source Expr or MVarContext value. The correction
changed only the test's owners; no runtime code or limits changed. A separate
parent rerun of that one case passed 13 assertions before the full control run.

The runner loads the independent model before the two test namespaces and adds
both count-guarded groups (119 total on this base). Full combined integration and
existing direct/Level/machinery/session regressions remain required after merge
with concurrent runtime units; these focused results do not enable full pass two.
