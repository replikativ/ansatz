# Void.mk release runtime unit

The engine implements the exact original `lean_void_mk` tuple:
`(erased owned, tobject owned) -> void`. The erased argument must be the canonical
zero placeholder; it is omitted from the native C call and never decremented.
The payload is consumed once. Native void uses the engine's existing object lane
and returns canonical zero. There is no new world carrier, synthetic guest body,
argument retain or Node field.

Pinned Lean 4.33.1 declares the opaque operation in
[Init/System/ST.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/System/ST.lean#L22).
Its [native helper](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/include/lean/lean.h#L3029)
performs `lean_dec` on the payload before returning boxed zero. Both authentic
original rows, including the owned boxed wrapper, are retained in the
[fixture](../test/fixtures/java-void-runtime/README.md). No adjacent world extern
is registered merely because a similarly named inline C helper exists.

Active explicit execution uses the existing native RuntimeAction. Before
claiming the payload, it publishes the argument packet, a retiring-value alias,
output zero and stage 2. It then calls the ordinary resumable release path.
Quiet destruction can finish inline; a Promise finalizer instead publishes its
existing release/resolve/task continuation, which can demand code, call Host or
fork. The outer Void action finishes only after that continuation drains.
`releaseClaimed` and the existing fork graph memo preserve exact disposition;
zero is not available through `takeResult` before cleanup completes. A callback's
Task result remains its own result and never replaces Void's zero.

Terminal cleanup failure preserves the pending runtime/Host/Code packet and
claimed release state. It does not make a second payload decrement possible or
claim that a failed engine has unwound, executed all finalizers, disposed or
closed. Diagnostic/scope retirement remains the caller's responsibility.

Inactive execution supports an explicit bounded quiet domain. Before a final
root decrement, a read-only identity walk checks positive owning storage,
including shared descendants whose multiple incoming edges could jointly retire
them. Persistent descendants stop traversal after their shallow liveness/owner
check. Object-array traversal uses live size; empty Ref slots are permitted.
Runtime Task/Promise metadata and unknown kinds reject before consumption. The
walk is limited to 100,000 identities and 1,000,000 owning edges, with interruption
checks. Immediate, persistent and nonfinal root decrements take the constant-time
path because they cannot dispatch cleanup. Immutable String/BigInteger carriers
have no physical RC here. These are named host-profile boundaries, not native
heartbeat accounting or a general concurrent-resource proof.

Root entry and saturated direct native AP perform the same checks before
entering the native call or retaining/deleting the closure. Both AP drivers are
covered. The intrinsic/FAP path validates before decrementing its payload.
An original guest wrapper can already have executed earlier ordinary guest steps
before reaching that FAP; rejecting there is not rollback of the caller. Ordinary
supported ready-only Tasks remain quiet in inactive mode; a foreign runtime Task
hidden inside a last-owner ordinary container is rejected before that container's
count changes. The tests include private foreign-owner/spare-capacity models;
they are not source-program admission or a general engine-membership guarantee.

The focused suite lives in `java-ir-baseline/void-checks.clj`. It covers authentic
ABI and wrapper calls, raw roots/FAP/AP, immediate and persistent values, surviving
aliases/cache credits, invalid preclaims, inactive quiet-domain boundaries, active
release forks and deferred finalizer Code/Host/fork/failure states. The parent ran the frozen suite in its existing 384 MiB REPL: 10 tests and 140
assertions passed in each recursive/explicit configuration, with no failures or
errors. The active cases explicitly enable the logical synchronous runtime in
either suite invocation. Reviewed Java source SHA-256 is
`c44766e9effbb8d3d61cae4d9ce920baa421bdfb593ef39b7299300cf1415192`;
immutable runtime jar SHA-256 is
`7472a9ca48cf1e88fc9d97ca54ffbbb24cd0289091702a0b6f3849d78ac0386e`.
Independent source review found no remaining blocker. No test JVM was launched by
the feature agent. No Init/image restore, kernel representation change, separate
native oracle or native performance parity is implied by this unit.

The complete isolated regression gate then passed 107 suites, 1,052 test
executions and 52,979 assertions at 384 MiB, exit 0, with no failures or errors.
The combined log SHA-256 is
`e7ff19b0d8ce00888e5176873654b70c95e24d482030eec12eaf00392f52c23d`.
It used the same reviewed Java source and immutable runtime jar. Separate
original-frontend command/EOF receipts and their cold/warm timings belong to the
integration experiment; this unit's gate is not a general file/import acceptance
or native execution/performance-parity claim.
