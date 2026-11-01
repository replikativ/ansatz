# Logical MT sharing and native exclusivity

This implemented research foundation models the pinned Lean multi-thread-enabled
marking and exclusivity rules in the single-threaded Java engine. It adds no
Promise, scheduler, task-manager profile, finalizer, native atomic operation or
public marking API. Source: Lean 4.33.1 commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Existing ready Task and synchronous release behavior remain
separate from any future active-task runtime.

## Owner counts and sharing mode are independent

For a live Node:

```text
exclusive = rc == 1 && !logicalMT
IR.isShared = !exclusive
refMaybeMT = rc == 0 || logicalMT
```

Positive rc remains the selected guest-owner count. Zero rc remains the existing
persistent profile; it is not a zero-owner live object awaiting collection.
Logical MT is monotone and remains true when a positive count falls to one.
Marking changes no owner count. Negative source counts are still unsupported;
positive imported counts do not infer MT state, and the graph importer has no new
sharing-mode field or kind.

Pinned `include/lean/lean.h:704–721` distinguishes native lean_is_exclusive from
lean_is_shared. Original IR isShared is the **negation of exclusivity**
(`library/ir_interpreter.cpp:620`, `LCNF/EmitC.lean:693–695`), so an MT count-one
Node and a persistent Node both produce true. Calling native lean_is_shared,
which returns false outside ST counts, would implement the wrong IR operation.

## Metadata, marking and forks

No common Node field is added. A lazy immutable SharingMetadata marker wraps the
existing kind metadata. An optional PointerMetadata always remains outermost,
preserving its observed identity word and branch owner stamp. Central kind
access unwraps both layers, so ArrayState, ByteArrayState and closure Generation
retain their existing behavior. No metadata wrapper owns guest values.

A null-kind marker can share one immutable singleton. Fork shares that immutable
marker or copies its inner kind state as required; mutable array/byte-array size
state still gets a distinct branch copy. Pointer metadata copies its owner stamp
to the child and preserves the observed word. Marking after fork changes only the
chosen branch's Node metadata, even when both branches share that observed word.
There is no side table retaining nodes or propagating flags between branches.

The private iterative markLogicalMT helper follows pinned mark_mt
(`runtime/object.cpp:663–729`): validate admitted values, stop at persistent or
already-marked Nodes, mark before descending, then follow owning edges. It visits
constructor fields, closure captures, ref payloads, live object-array elements
and ready Task values. ByteArray payload and immutable Java String/integer
carriers are leaves. Spare object-array capacity is not traversed. The marker
itself handles duplicate edges and cycles; no Java recursion is used.

The only admitted ST Task shape is ready. An impossible ST-pending shape rejects;
this is not pending-task support. Empty refs remain valid and can be marked;
existing empty get/take/swap behavior remains an explicit unsupported/blocking
profile error. This walk is synchronous and has no guest callbacks or budget
suspensions. A malformed late descendant or allocation failure can fail the
branch after a monotone marking prefix; there is no rollback or publication claim
for that failure. Future pausable marking needs an explicit action/continuation.

## Existing publication and uniqueness sites

Pinned `runtime/io.cpp:1448–1529` treats both MT and persistent refs as maybe-MT.
Ref.set/swap therefore mark the incoming payload before publishing it when
refMaybeMT is true. Fresh ST refs, including refs with several ST owners, do not
mark their incoming payload merely because their owner count exceeds one.

No registry signature changes: set/swap still take
`[erased, erased, borrowed tobject ref, owned tobject value, void world]`, returning
`tagged` Unit or owned `tobject` old value respectively. Original proof/world
placeholders and genuine boxed-wrapper ownership remain unchanged.

Ref.set follows the native branch order: ST releases its old value before storing
the incoming value; MT/persistent marks and stores incoming before releasing old.
Ref.swap marks where required and transfers the old owner without decrementing
it. These are still finalizer-free synchronous helpers. No deferred callback,
release-frame or resumable native-operation guarantee is implied. Fresh refs,
Task.pure, the no-manager ready-map fast path and fresh copy-on-write results
start ST; an ST parent may contain an already-MT child.

All current exclusivity consumers use the centralized predicate:

- Constructor SET/SSET/USET/SETTAG and DEL/shell transfer reject MT count-one
  mutation; compiler reset paths can choose their existing shared branch through
  the corrected IR isShared result.
- Both closure application drivers retain captures and decrement an MT count-one
  closure rather than taking the unique ST shell-transfer path.
- Object-array copy/growth/pop/set/swap and ByteArray push/copy treat MT count-one
  inputs as nonexclusive. Fresh copies are ST; their MT children remain MT.

INC/DEC, zero transitions, generic release worklist capacity checks and known
argument/capture/alias credit totals continue to use raw positive counts. In
particular, a raw rc==1 final-edge capacity preflight is a credit check, not an
exclusivity check. No owner ledger comparison is changed to use exclusive.

## Verification and boundaries

The separately compiled Java 11 jar passes in a retained 256 MiB REPL. Twenty-one
new private-foundation tests pass: 205 recursive and 214 explicit assertions.
They cover monotone and persistent stops, cyclic/deep owning graphs, every
supported Node kind, persistent/MT/ST ref publication, all constructor uniqueness
operations and reset selection, object-array mutation/copy, ByteArray spare
capacity/fork, closure capture accounting/generation, pointer wrapper order and
foreign-owner guards, branch-local marking, ST ready-map/pure behavior and an
impossible ST-pending diagnostic shape.

Existing Ref, object-array, ByteArray, Task.map, pointer, generation, baseline and
continuation suites pass in both relevant drivers against the same isolated jar.
Tests reuse their original pinned source fixtures; no ABI, expected oracle value,
source count or fixture is changed for this feature. The runner includes both
new suites and expected test counts.

Prepared graphs remain under their existing RC0/selected-owner profiles. This
feature does not authenticate or import native MT sharing mode from old captures,
collect RC cycles, execute finalizers, promise concurrency, or establish complete
frontend command elaboration. A future active task implementation must supply all
additional native marking/publication sites and resumable release boundaries
before making those claims.

Root integration: the complete Java 11 isolated-jar gate exits 0 at 384 MiB,
794 test executions / 22,201 assertions across 83 suites. Independent native
marking/metadata/exclusivity review found no blocker. Existing ownership-credit
checks, including the release worklist's last-credit capacity preflight, retain
ordinary positive-count semantics.

The original demand-loaded header frontend was also rerun in the retained
384 MiB REPL. Its default case completes with 701 original bodies / 312,634 IR
instructions, and all twelve native header-oracle cases still match error
status, UTF-8 end byte and rendered diagnostics. This exercises the new sharing
behavior during real frontend work; it does not establish command elaboration
or active task support.
