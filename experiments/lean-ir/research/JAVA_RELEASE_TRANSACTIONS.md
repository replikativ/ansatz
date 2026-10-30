# Budgeted explicit root release transactions

The experimental interpreter exposes `startRelease(value, count)` for its
existing explicit, finalizer-free profile. The research facade adds
`start-release!`; the existing `advance`, `phase`, fork and `takeResult` APIs drive
it. This is a root disposal operation, with no fabricated guest Function, body,
Program slot or PC. It does not enable an active task runtime.

Start validates an open idle explicit engine with no pending result or release
work, a nonnegative int count, the existing guest-carrier discipline, and enough
positive RC credits. Persistent live RC0 values retain their existing quiet
semantics. Validation applies even for count zero: Object arrays, Double, private
F64 control packets, arbitrary host objects, null and dead Nodes do not enter.
Pointer-observed and closure provenance follow existing guards. This is not a new
universal proof that an arbitrary unstamped Node reference belongs to a branch;
complete, correctly owned caller credits remain a precondition.

Immediate values, persistence, zero-count and decrements leaving positive RC can
complete Unit at start without allocating a transaction record. A zero-owner
graph gets a preallocated private record before its root credits are consumed
once. The record retains origin/count/claim disposition, current retiring shell,
field cursor and field limit. Queued zero shells are dead, distinct from live
persistent RC0, and still own their not-yet-scanned fields.

`advance` charges one work unit for one field edge or a zero-shell
selection/completion transition. `advance(0)` does no pending work. Fields scan in
ascending order; each credit is consumed immediately, and the field clears only
after that succeeds. A child is not visited until the parent's entire batch has
finished; zero shells are then selected LIFO. The transaction and synchronous
DEC call the same production field-credit and queue-pop helpers. Array spare
capacity stays nonowning, duplicate occurrences consume distinct credits, and
deep graphs use no Java recursion. `instructionCount` reports these engine work
units during a release root, not original guest body instructions.

Completion clears the private transaction and work queue, and ordinary
`takeResult` transfers canonical Unit zero once before returning to idle. A
completed Unit can be forked or closed safely without dereferencing a source
entry Function or acquiring a guest Node owner. In the existing finalizer-free
profile close continues to handle its ordinary private result/cache/stdout
owners; this does not implement active-mode cache disposal.

Fork uses the existing single memo for retiring/current/queued shells, remaining
fields, external roots and the private record. RC values and claim/cursor state
copy exactly; copied diagnostic links create no owner credits. Pointer words
preserve their identity with child provenance retargeted as before. A child
continues only its remaining edges and drains independently. Failure after claim
is terminal: the current cursor, queue, origin and still-owned fields remain
available, with no unconditional work-array cleanup. Failed-state fork, close,
new entry and result extraction reject. Synchronous public DEC rejects before
mutation until a release root's Unit has been taken or its completed root closed,
preventing reuse/corruption of that work buffer, including after failed release.

Default synchronous DEC stays allocation-free with respect to continuation
frames and remains the fast finalizer-free path. The optional facade method
lookup preserves loading of older benchmark jars; requesting the new API on an
older artifact reports its absence. Helpers, IR DEC, HostCompletion cleanup,
public active-mode release, Promise finalizers and native nested kind barriers
are **not** made resumable by this root API. Future `QUIET_COMPLETE` versus
`NEEDS_DISPATCH` helper control still needs typed operands/suffixes, callback
entry, stacked cleanup records, logical MT and explicit active-profile disposal.
No thrown suspension sentinel or guest finalizer callback is introduced here.

The focused suite covers preflight and illegal entry, zero/single-step budgets,
quiet cases, shared/duplicate/persistent/deep/wide graphs, pointer/closure guards,
midbatch alias forks and dead queued shells, failed-edge/field-limit ownership,
Unit completion and private cache close. Modeled malformed heaps are failure
accounting tests, not admission claims. See [native ordering](JAVA_RELEASE_ORDER.md)
and the separate [logical task contract](JAVA_LOGICAL_TASK_RUNTIME.md).

Root integration: the complete isolated Java 11 jar gate exits 0 at 384 MiB,
806 test executions / 22,538 assertions across 84 suites. Independent source,
claim/cursor, fork and result-lifecycle review found no blocker in this scope.

A retained REPL also constructs a genuine Lean Environment by executing 196
original demand-loaded bodies, starts its release on a fork, pauses after two
of its eight root fields, and forks again. Both branches complete identically:
12,358 release work units and 13,920 release credits, Unit result, empty worklist,
and cleared dead environment fields. The original parent's environment remains
live at RC1. All external owners are included in both forks. This checks real
frontend-produced data at a 384 MiB heap limit; it is not Promise callback support
or a native timing comparison, and performs no full image/Init replay.
