# Checked source-module Base view

The deferred `source-base.clj` issuer opens a lazy checking view only from the
actual source exchange's opaque SourceClosure and FinalizedSourceRun, plus a
fresh strict fixed Prelude Base. It accepts no caller-created Java Env or CI map.
The existing fixed `base.clj` checks and paired Prelude store profile are unchanged.

Opening checks every constant returned by the actual source finalizer: the
domain must be exactly the disjoint union of the fixed Prelude and the checked
source segments. Source entries retain their exact Java ConstantInfo identity
and immutable checking snapshots; finalized guest entries must have the same
typed Name, kind and original payload identity. Prelude entries use the existing
strict original-payload validator. Duplicate, missing, extra and substituted
entries reject before a SourceBase is issued. Limits are 4,096 source CIs,
512 checked segments and 6,410 total constants; these are independent fail-closed
bounds, not general library-size claims.

The Java Env has an uncached external resolver. Source lookup returns the
already checked Java CI; Prelude lookup delegates to the existing guarded lazy
store view. It does not eagerly hydrate all Prelude declarations or replay
proofs. Full issued closure/Run graph and snapshot checks bracket each complete
metadata borrow. Those issuer borrows also prohibit advancing the guest while
the checking view is borrowed. Per-CI and resolver checks require positive
private borrow depth and check thread, lifecycle, current driver Program,
CodeReceipt/source lease and the fixed Prelude view. They do not walk the full
module graph for each CI. A retained Java Env cannot be used outside that borrow.

`assert-session!` binds the view to the exact engine, SourceBinding and actual
new FinalizedSourceRun. Existing authority still needs the real HostGuest
root/map/quot observations before a checked association; opening this view
does not perform that association. `revoke!` invalidates only the view and
rejects during an active borrow. Actual source ModuleData, region, Run and
Prelude owner occurrences stay with their explicit lifecycle controllers.

The reconstruction issuer and its normal original finalizer execution are a
separate unit. This source checkpoint does not seal an existing Env or fabricate
initializer/extension parity. Fresh strict Prelude Base issuance follows old
adapter retirement, since a revoked Base cannot be revived. Complete source
ModuleData witnesses and actual source finalization must remain live throughout
this view's lifetime.

Nine model families cover forged tokens, exact checked segment domains,
mutation, original payload readback, complete final domains, scoped lazy lookup,
session/version binding and exceptional/revoked borrows. A failed issuer check
inside an active borrow still decrements its outstanding depth on unwind, so
view-only revocation remains possible without reviving the failed capability. Issuer and lifecycle
mocks are explicitly labeled; they do not constitute actual source reconstruction
acceptance. No worker JVM or native execution was used to author this unit.

Coordinated validation: the parent definition-loaded these exact files in the
retained JVM and ran all nine model families: 61 assertions, zero failures or
errors. The external receipt is
`target/java-source-exchange-v1/source-base-model-results-v2.edn`.
This is model acceptance only; no source closure or reconstructed Base was
issued by that run.
