# Proposed artifact-relative Prelude declaration adapter

This is an implementation delta against the experimental v3 adapter/authority in
`target/java-incremental-declaration-v3/`, read alongside
`target/java-logical-init-association-v1/ASSOCIATION_API_PLAN.md`. It describes the
next source unit after genuine finalization. The root-produced v14 receipts now
record genuine original finalization, quotient 1/empty 0/count 2,314, and exact complete
store checking-shape correspondence for all 2,314 actual finalized CIs in 73 batches
of at most 32. The recorded semantic comparison took 3,871.73 ms. These are concrete
runtime observations, **not** an issued in-process finalizer lineage or association.
This reviewer only read `target/java-prelude-finalizer-v1/actual-finalizer-v14.edn`
and `target/java-prelude-pair-activation-v1/actual-finalized-map-complete-v14.edn`;
no JVM/native operation ran here. Keep strict-empty v3 and its bootstrap issuer
unchanged. The next admitted run needs a sealed wrapper from before start; do not
retroactively turn v14's descriptive receipts into authority.

The first target remains the exact private Prelude domain, currently 2,314 names,
then a safe noncomputable Nat identity and its reflexivity theorem. This is an
artifact-backed preloaded import profile, not ordinary default Init or arbitrary
project loading.

## Separate the three authorities

| Authority | Actual evidence it must bind | What it does not establish |
| --- | --- | --- |
| Composite code receipt | Accepted catalogue, both ordered overlays, actual common SourceBinding, canonical registered Headers, authentic pending/completed local value startup | Imported kernel contents or a valid guest Env |
| Paired producer/store token | Same native producer/build/module cohort, selected genuine module parts, exact typed CI inventory, complete checking correspondence, captured format 2 roots and actual source/store leases | Execution of original Java finalization or ownership of its result |
| Finalized-prefix lineage | One actual original finalizer root invocation and result under that source/engine, matching admitted module/request owners, actual K/M/quot/header/module witnesses and retained occurrences | Replay/typechecking of imported assumptions or authority to execute imported IR |

Only their combination may issue a new private `MatchedBase` token. Neither a
caller map with `:verified true`, an equal receipt, Env.size, a source SHA, nor
`guarded-kernel-view/open-resolver-view!` can issue it. The existing World artifact
issuer is not a substitute: it requires an eager projection and World ownership.
New weak-registry entries must not retain their own token key. In particular,
a view lease callback must capture a private state holder, not close over the
MatchedBase token whose registry entry owns that view. Session versions may retain
the separately issued base token while their associations are alive.

## Authenticate the finalizer result before the first declaration

Prefer deferring **association helper acquisition** until the first real unclaimed
`lean_elab_add_decl` HostRequest. Reuse that request's genuine HostGuest root/map/
quot/checkedConstants tokens. This avoids inventing a HostGuest result for a
normal pre-frontend root invocation.

A separate trusted root-driver wrapper must nevertheless own the finalizer run:

1. Before start, create an internal pending record tied to the actual engine,
   current Program, common SourceBinding, registered finalize Header and owned
   assembly state/import request occurrences. Require the real completed local
   value startup and the accepted captured runtime/initializer coverage.
2. The wrapper starts that exact normal root call and records its actual progress,
   Code/Host pauses and terminal outcome. A call count or copied descriptive
   receipt cannot replace this wrapper's private pending identity.
3. On genuine completion, the same wrapper takes the actual owned IO result.
   Validate the compiled **IO success** representation and its Env field; do not
   reuse the publisher's `Except.ok` tag assumption. A failed/pending result
   cannot produce lineage. Record the actual owner transfer before inspection.
4. Extract K/M/quot/header/module witnesses through the accepted compiled-layout
   reader while paused. Retain K and M as explicit host occurrence slots before
   relying on their identities. Retain the actual final Env/result ownership as
   required by the caller's frontend handoff. Keep module/source/virtual-region
   owners and leases alive; never send virtual regions to native free/read FFI.
5. Seal a private `FinalizedPrefix` pending association. Source/layout/read-only
   witnesses describe this exact result and owner ledger. They are not caller
   hashes over arbitrary current Env pointers.

If the existing finalizer runner does not expose a trusted start/take-result
integration point, add that narrow wrapper first. A new `issue-lineage(env,
receipt)` function called after an unrelated invocation is insufficient.

The first real ELAB request may carry an authenticated header/diagnostics-only
view. Its taken root/map/quot helper results must agree with the protected final
map/quotient and import/module profile; its Env pointer need not equal the original
outer Env pointer. Unknown nonempty maps refuse. Keep both the prefix anchors and
new helper occurrences until the association commits; then release the redundant
prefix occurrences through the existing explicit retirement path. Equal Node
values do not mean equal owner occurrences.

## Build one cheap original-payload index

While the admitted ModuleData aggregate is still owner-backed and the engine is
paused, enumerate the genuine selected private `constNames/constants` arrays.
Use `imported/project-constant-name-kind` and the same carrier ops to record:

```
exact Java Name -> {eight-kind tag, actual CI payload Node,
                   actual source part/array entry, authenticated producer key}
```

Use actual imported Array fields/owners, not a reconstructed native address or a
source-ID-to-Node table invented after PreparedGraph installation. Source IDs can
identify producer records only after they are tied to the actual converted root.
The complete five-part admission remains authentic; the selected private domain
must follow the original finalizer's mode, not a synthetic empty-part selection.

Validate every array length, exact typed Name, duplicate, domain and kind against
the paired producer's accepted inventory. Reject display-key collisions in the
base store domain. This reads Name spines/layouts, not all Expr/proof bodies.
The authentic const2ModIdx inventory also includes compiler-only/IR names: compare
it to its own admitted source inventory, not to just the 2,314 checked CIs. Do not
sum the 1,188 extra-name count with the CI count without accounting for overlap.
Close every Node projection scope and clear every derived imported-CI memo before
any guest advance.

At the first actual `checkedConstants` result, require exactly the full base
inventory, each genuine kind and original payload identity. The helper token must
prove that the array enumerates this actual checked map, not an arbitrary host
array. A distinct ConstantInfo wrapper may be harmless if its actual validated
payload identity agrees. For this first profile, reject a reconstructed payload.
A future fallback needs an independently bounded **complete** semantic comparison;
never turn a pointer mismatch into unchecked acceptance.

Imported guest payloads remain private, source-owned immutable data under the
accepted original-code/host mutation contract. Name/kind/identity enumeration is
not a detector for arbitrary host mutation inside an unchanged payload's Expr
DAG. Prohibit such mutation and unaudited guest writes. On hydration, additionally
compare the actual source payload's full checking shape to the store CI. Wider
metaprogram/project-loading capabilities need their own source-effect audit.

## Proposed API and private records

These names are proposed new functions, not existing public capability APIs.

| New module/function | Private input/output contract |
| --- | --- |
| `finalized-prefix/begin!`, `take-success!` | Trusted normal-call wrapper owns actual finalizer progression; emits only an opaque finalized-prefix token with retained occurrence slots |
| `matched-base/open!` | Takes issued paired-producer and finalized-prefix identities, actual driver/setup and borrowed store lease; creates a **pending** base with original-payload index and private guarded view |
| `matched-base/claim-seed!` | Consumes the first request's real taken helper bundle and owned K/M/readback slots; validates complete inventory and finalizer lineage; installs version 0 exactly once |
| `matched-base/guard!` | Checks live source/Program/engine, source/store/region leases, retained owners, actual expected quotient/profile and the entire growing Java materialized ledger |
| `matched-base/with-check-scope!` | Opens one paused-engine Node scope and bounded imported-CI projector for one synchronous Java checking boundary; clears all memos before closing/advance |
| `matched-base/with-version!` | Guards before and after a trusted operation using a private version Env, including on exceptional return; no Env escapes to unguarded callers |
| `matched-base/revoke!` | Revokes authority/view first; returns or preserves actual retirement owner packet; never closes a shared borrowed store |
| `artifact-declaration-session/open!` | New v4 session accepts only the issued base token and existing checked HostGuest setup; has no fresh-empty bootstrap parameter |

A base entry holds the issued identities, actual engine/source/setup, expected
layout/import/module/quotient facts, source-payload index, shared guarded view,
lease guard, and private initial owner slots. It holds no eager map of all Java
CIs. A version holds parent/id, its actual K/M owner slots, same base token/view,
quotient, exact local CI/payload maps, local snapshot segments and explicit counts.
The adapter's invocation ledger still owns temporary helper/publication/release
occurrences. Preserve the producer's exact typed axiom/unsafe inventories and
actual quotient assumptions. Every version remains `:base-basis :trusted-artifact`
with the same opaque base admission and explicit strictly checked local additions;
an imported unsafe declaration never relaxes the local safe-admission policy.
None of these descriptive record shapes is issuance authority.

## Integrate the existing guarded full-value view

Use `guarded-kernel-view/open-view!` against the actual borrowed captured store
and authenticated `root-fields`, exact base Name domain and finite evidence
limits. It already avoids ordinary unbounded load-env hydration: only bounded
`storage/full-ci-evidence` on its private backing view constructs a missed CI.
Its outer Env is uncached and has no copied evidence extension.

The trusted `:authenticate-ci!` callback must require the current synchronous
checking scope, fetch the indexed **actual source CI**, and project that one CI
through `imported/make-constant-projector` with the scope's carrier ops. Compare
`imported/checking-shape` for all eight variants, including exact binder metadata,
full theorem/opaque values, hints, safety/all/family/rules. Keep the current exact
comparison and existing bridge projection normalizations, including documented
MData erasure and Level normalization; this is not byte-for-byte native AST
reconstruction. Do not add another erasure to make a mismatch disappear. Do not replace it with Lean Expr.eqv, a body hash that omitted binder
metadata, a caller flag or a defs-only CI. The producer's ExprStructEq cache fixes
are part of paired-evidence acceptance, not permission to weaken comparison.

The view checks lease/thread/lifecycle on every hit and captures CI/container
witnesses before calling authentication, then rejects mutation during it. Guard
its complete historical ledger at every outer boundary. Cache hits need no new
full source projection. Misses outside a live checking scope refuse.

Keep all version Envs private. `.addConstant` preserves the same uncached external
closure across descendants, but local lookup occurs before that closure. Thus
`guard!`/`with-version!` before and after every checking/helper/publication step is
mandatory even when no base CI is looked up. The source/store lease callback
must validate actual handles/session state; branch labels and `close-store`
are not revocation. Split the internal live-source/owner guard from the complete
base guard: the view lease callback uses the former, while the latter calls
`view/guard!`. Calling the complete base guard from the view lease callback would
recurse forever. Never recursively call `validate-segment` from an external
lookup; use `validate-segment-values`.

## Exact delta against the v3 adapter

| Existing v3 seam | New artifact-relative implementation |
| --- | --- |
| `open-session` bootstrap callbacks | Accept `MatchedBase`; retain existing finite kind/fuel/projection/local-publication permissions; no legacy fresh-authority factory |
| `source-live!` / authority `live-driver!` | Composite receipt/common source/current Program/catalogue guard plus matched-base lease/owner guard; no hardcoded zero-action source profile |
| `retain-seed-version!` | Claim authenticated private lazy base and actual taken K/M slots; version 0 has `baseCount=2314`, `localCount=0`, authentic quot and zero strict local publications |
| `resolve-base!` | Match actual input map/quot to exactly one retained version under the same base token; support authenticated header-only views; no empty-map fallback |
| `validate-versions!` | Validate every K/M occurrence, expected quot/source/base identity, shared historical base ledger, each version's local snapshots and exact local domain |
| `validate-candidate!` | Same base/view/quot plus exactly parent local map + one CI, new segment and actual local payload; never `validate-segments` on an external Env |
| `check-java!` | Enter fresh scope, reject exact base-domain/local name collision, run unchanged strict bridge admission, preserve external view/quot, snapshot only the new local CI |
| `validate-readback!` | Enumerate full `baseCount+localCount` guest map within explicit bound; base entries use original-payload index, local entries use existing kind/payload/full checking-shape rules |
| `commit!` | Transfer actual candidate K1/M1 occurrences only after all guards/readback pass; preserve old versions, shared base token/ledger and trusted-artifact provenance |
| `poll!` quot/empty stages | Compare real taken quotient result to the issued base's expected quotient. The original empty getter may be checked against false as a diagnostic, but cannot seed authority |
| `take-retirement-owners!` | Revoke session/base view first; transfer all distinct owner **occurrences**, including seed/history/prefix/source owners, through existing resumable cleanup |

Reuse `launch-helper!`, `receive!`, occurrence slots, Code/Host request service,
`cleanup-next!`, `reply!`, terminal failure handling and the driver loop semantics.
Do not introduce nested public invoke, a second scheduler or another evaluator.
A tracked common owner/protocol core can be factored from v3 with equivalence
tests, or a separately versioned narrow wrapper may initially retain that reviewed
logic. Do not silently change the strict v3 wrapper's source or empty rules.

Validate local domains without accidentally hydrating the base:

* Build the actual local map from `Env.allConstants`, compare exact Names and CI
  identities to the version's local map, and confirm with `lookupLocal`.
* Require no intersection with the exact base domain; preserve `sameExternalView`
  and authentic quotient. Validate local snapshot **values** independently.
* Do not use Env.size or validate-eager-domain. With 2314 external declarations,
  zero and one local declarations both give Env.size 2314; total counts are 2314
  and 2315 respectively.
* Track global publication budget separately from a version's local count. If an
  older accepted map is used as parent, publication id 2 may have localCount 1,
  not 2. Each version's parent and local overlay determine its readback domain.

The first bounded readback may inspect 2314 + at most 16 entries each publication.
Imported entries do not trigger Java proof hydration. Preserve the complete base
set on readback; filtering to local entries would miss removal or replacement of
imported declarations. A scalable map-delta proof is a later optimization.

Retirement order must distinguish revocation from physical source release. First
forbid further checking/publication and close the Java view. Keep the runtime
code lease, region lifetime handlers and required guest source owners valid while
resumable releases drain their actual occurrences. Drop those leases only after
cleanup finishes. A closed base view must not prevent ownership-only cleanup, and
a revoked store must never be reopened to make checking succeed again.

## Negative gates before the Nat acceptance

1. Copied/forged source, producer, prefix or base receipts; correct source SHA but
   foreign engine, wrong Program/Header, unexecuted value startup, wrong actual
   finalizer arguments, pending/error/replayed normal result, or wrong IO layout.
2. Changed part/import order, omitted one of five parts, wrong selected private
   domain, duplicate typed Name, display-key collision, any CI-kind mismatch,
   missing/extra finalized map entry, reconstructed/foreign payload, or changed
   quotient/header/module/const2ModIdx witness.
3. Valid producer/store data attached to a different finalizer map; valid finalizer
   paired with different captured roots; changed branch head must not redirect a
   live captured view. An unrelated Mathlib declaration remains invisible.
4. Lease retired on a memo hit; wrong thread; hydration outside its Node scope;
   closed or advanced Node projector; wrong typed returned Name or missing domain
   member; per-CI/depth/aggregate materialization budget exceeded.
5. Java CI/safety/hints/all/rule-array mutation, or CONST universe-array mutation,
   after hydration or on any old version. Grow the base memo while checking v2,
   then mutate that new entry and attempt a v0 operation: the shared ledger must
   reject it. Never recapture a mutation as a new snapshot.
6. Base-name or parent-local-name collision; definition/theorem checking failure;
   changed external-view/quotient; extra/changed/removed local CI; header-only view
   with a different map. Refuse before original publisher when possible.
7. Publication succeeds but any readback/guard fails: terminal refusal with actual
   publisher reply and temporary owner escrow retained, no retry or success reply.
   Cleanup Code/Host pause, failed release and already transferred HostCompletion
   preserve the existing v3 ownership protocol.
8. Double seed claim, replayed HostRequest/helper token, known map with retired K/M
   owners, inherited-base provenance changed to strict-fresh, duplicate retirement
   of an aliased owner value, active association fork, or shared-store close by a
   retiring child.

Only after these source boundaries and an actual finalized seed are accepted,
run the original frontend Nat identity/reflexivity pair to EOF with strict local
checking and complete retirement. Generated IR authorization, ordinary literals,
new module initializers, filesystem imports, Mathlib selection and general
project loading remain separate capabilities built on the same captured-root
and exact-publication contract.


## Smallest implementation and review units now

1. **Seal the actual normal-call lineage.** Add the narrow trusted finalizer-run
   wrapper and a fresh-run probe. Review start/take-result identity, IO.ok layout,
   actual argument owners, startup/source/region leases and failure escrow. Reuse
   the successful v14 route as the oracle; do not claim its old observation maps
   were opaque tokens. This unit changes no TypeChecker or declaration adapter.
2. **Issue the pending matched base.** Add one private holder/registry, complete
   actual Name/kind/payload inventory and the guarded-view integration. Reuse the
   v14 bounded 32-CI correspondence routine under the new sealed orchestration if
   full correspondence is revalidated during preparation. Discard each batch's
   temporary Java CIs; do not retain a map of 2,314 proof-shaped snapshots. Test
   forged tokens, wrong roots/map/domain/quotient, revoked memo hits, mutation,
   scope closure and no key-retaining callback cycle.
3. **Port the declaration delta only.** Create a separately versioned adapter/
   authority around the reviewed owner/request machinery. Replace precisely the
   v3 seams in the table above; keep its three strict admission functions and
   publisher operations unchanged. Test a nonempty 2314+0 seed, then 2314+1 and
   2314+2 maps, plus an old-parent branch where publication id 2 has localCount 1.
   Review every before/after guard and owner transfer, not just successful output.
4. **Bind the real first request and run the Nat pair.** The real ELAB helper bundle
   claims version 0, then the original Nat identity/reflexivity commands strictly
   check and publish relative to that base, reach EOF and retire every owner/
   source/store handle. Keep observations labeled trusted-artifact base plus
   strict local additions. No whole imported library replay is needed.

The first two units can remain small and independently reviewable. The third is
an explicit finite adaptation of an existing state machine, not a generic new
certificate framework. General project loading should later select a genuine
module closure and captured root domain through the same interfaces; it must not
obtain a broader Java lookup domain than the actual guest constant map.
