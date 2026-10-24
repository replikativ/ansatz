# Explicit managed-operation abandonment

The composed lower-level suite passed **95 tests / 1,390 assertions**, including
declared binding-helper protection. The [validation record](../measurements/managed-operation-disposal.json)
records the bounded source-level run. These
optional APIs are not a Project failure-disposal feature or production release.

`raw/abandon-host-boundary!` permanently retires an unstarted issued boundary
without dispatching its handler. Already consumed/failed/abandoned tokens are
safe to retire again; running completion rejects disposal. No effect is undone
and a caller deliberately branching an old raw World is outside this protocol.
A private weak-key/scalar-phase registry is the authority; the public deftype
claim Atom is neither read nor written. Attached hooks, claim resets and copied
constructor fields cannot dispatch or revive a retired/unissued token. Completion
and retirement claim under the same token lock; registry values retain no World
or key. Existing invalid-option, helper budget and canonical error rules remain.

`resident/abandon!` retires one Context wrapper. A weak-key/constant-value
tombstone blocks future Context operations without writing its public state Atom. It does not execute guest code, sweep uncertain RC owners or close
a borrowed Source/Store. Parent and separately forked wrappers remain live.
Publicly attached Atom watches/validators and substituted state holders reject
before retirement. Even a concurrent hook installation cannot be triggered by
retirement: it performs no Atom reset. Keeping the wrapper/old Atom keeps its
diagnostic data as caller-owned retention; library tombstones do not root it.
Normal successful `resident/close!` remains unchanged.

`dispose-import!`, `dispose-source-graph-import!` and
`dispose-native-init-base!` accept their fixed issued controls. They reject busy
or foreign-mode operations, poison unstarted boundary tokens, abandon any
untransferred adopted Context and replace the continuation with a small disposed
receipt. Completed successful controls have already transferred their Context;
disposing those controls does not revoke that returned owner. Double disposal is
idempotent. Advance/finish cannot restart a disposed operation.

A failed backend can publish only a lower-bound checkpoint. Therefore disposal
abandons the whole private branch instead of guessing RC drops from argument,
assembly, IO or result-owner stages at different checkpoints. This is a managed
JVM-heap operation, not native Lean external-object finalization. Guest-owned
foreign resources need a separate exact-once host-resource contract; current
borrowed native Sources/Stores/leases stay with their external owners. Arbitrary
host effects, completed initializers and successful publications are not rolled
back or replayed.

A disposal failure remains terminal and preserves pending state and the original
operation failure. It does not authorize cleanup/operation retry. Successful
disposal removes the library registry's heavy continuation roots. A caller that
retains the original Throwable/ex-data or copied World still owns those strong
references; no heap/GC reclamation promise follows from a scalar disposal receipt.

[Project failure disposal](PROJECT_FAILURE_DISPOSAL.md) adds a separate shared
owner ledger and opaque failure-capsule API, including invocation/open failures.
Direct resident-call exceptions remain caller-owned diagnostics; input Context
is borrowed and is not abandoned by observing an error.

Tests use tiny real raw execution and public resident controls across the three
backends. Imported compiler/factory transports are explicitly modeled; those
checks do not establish genuine full frontend acceptance. Coverage includes boundary replay prevention, hook rejection, parent/returned-owner
preservation, fixed-mode/busy rejection, failed original-cause retention and
bounded library tombstones. The composed run used a 384 MiB heap and
768 MiB process-group RSS cap, took 40.137 seconds and peaked at 514,895,872 bytes
for the guarded process group. All 700 input pins matched after process disposal.
No native or full hosted frontend was launched.
