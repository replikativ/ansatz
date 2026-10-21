# Scoped source reconstruction during import finalization

This describes the optional experimental reconstruction profile and its remaining
acceptance work. The completed-import profile still requires an actual checked
target association and its completed source import receipt. The distinct
reconstruction profile permits selected imported source code only inside an issued
finalizer attempt, using the original checked publication as provenance. It does
not issue an early target association or completed import receipt.
The earlier ordering [regression record](../measurements/source-reconstruction-ordering.json)
records **892 tests / 90,162 assertions**, plus focused controls on all three
backends and an ordinary-classpath runner load. It distinguishes source-derived ordering from actual hosted frontend evidence.

The [runtime implementation record](../measurements/source-reconstruction-runtime.json)
records **16 focused tests / 601 assertions** across three backends and the complete
**911-test / 91,056-assertion JVM campaign**, with independent code review.
Genuine hosted macro import and edited-branch acceptance remain separate gates.

## What is established

At pinned Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
`Lean/Environment.lean` constructs the imported constant maps before
`finalizePersistentExtensions` returns the Environment. In
`Lean/KeyedDeclsAttribute.lean`, `ofOLeanEntry` calls `env.evalConstCheck` while
reconstructing extension entries. Source macro code can therefore be needed
before completed finalizer IO and the later fresh kernel check. This ordering
comes from upstream source; it is not a recorded genuine imported-macro failure.
See pinned [finalizeImport](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Environment.lean#L2307)
and [ofOLeanEntry](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/KeyedDeclsAttribute.lean#L118).

The focused tests model a staged finalizer callback with the complete native+A
constant values, before its final IO result. The unchanged completed-import
authorization rejects that transition and preserves the terminal checkpoint/session without replay.
A separate control completes the real modeled finalizer and fresh Java check,
then removes only A's import receipt: the same checked target still rejects.
Restoring the original receipt authorizes. This isolates receipt dependence from
absence of a checked target association. A third test runs actual raw evalConst
witness transport for an admitted local compiler unit with no publication/import
receipt and confirms that complete witness provenance alone does not grant
imported source authority. These are model frontend/finalizer fixtures, not a
native macro-import acceptance run.

The [local macro record](../measurements/native-local-macro-runtime.json)
independently exercises actual source syntax expansion. Its closed result has a
value initializer and uses explicit initialization before calling it. It does
not establish imported macro reconstruction or justify enabling initializers in
the reconstruction profile. Import acceptance fixtures use functions such as
`Nat → Nat` and `String → String`; their actual hosted action vectors must still
be inspected, even when native export has no actions.

## Public experimental boundary

The implementation lives in the optional `prototype.resident-init-prefix`
namespace. Its private prefix certificate, issued operation registry, active
reconstruction scope and cooperative driver share that ownership boundary. There
is no public arming function or caller-supplied proof map. The explicit APIs are:

```clojure
;; Before preparing the independent native configuration and issuing its prefix:
(prepare-reconstruction-profile exporter eval-options helper-configuration)
;; => {:profile opaque-profile :eval-binding exact-host-created-binding}

;; Admit that exact binding and the helper roots before issuing the prefix.
;; A is compiled/published once; proof helpers have their own explicit budgets.
(publish-source-for-reconstruction
  context source-request issued-prefix opaque-profile publication-options)
;; => ordinary publication result plus :reconstruction-publication capability

;; Import B using the capability from that actual A publication:
(prepare-source-reconstruction-import-over-init
  published-context import-request issued-prefix opaque-profile
  reconstruction-publication import-options)
;; => the existing staged {:control ... :progress ...} shape

(advance-import! control limits)
(finish-import! control)
```

The profile constructor supplies a delegating evalConst binding. Completed
imports continue through the existing narrow source-import validator. The new
path is armed privately only during that issued control's start, advance or host
boundary completion. Its exact binding must be admitted before prefix issuance,
and the prefix's independent configuration must capture that same binding object.
It cannot replace or expand an existing issued prefix's binding authority.

For reconstruction controls, existing progress reports include a descriptive
`:reconstruction` audit after successful row authorization. `:authorization-count`
counts authorized witness rows, not macro invocations. Distinct actual requested
primary names are capped at 64 entries and 4,096 characters per name, with
truncation marked. The module and unit digest identify the attempt; the digest retains its final
file-handle meaning even when a callback row belongs to an earlier unit. These fields
grant no authority; observers still run only after the private scope is disarmed.

The [hosted unit diagnosis](../measurements/source-reconstruction-unit-diagnosis.json)
records a successful initializer-free A publication with five units followed by
a terminal imported-finalizer failure and zero row authorizations. Both macro
primaries belonged to earlier units; neither belonged to the final-handle unit.
It is failure evidence, and does not establish hosted imported macro acceptance.

An actual hosted publication can contain several compiler units: source macros
may be compiled during elaboration, before the final file-handle unit. The
reconstruction publication captures the exact successful before/after admission
delta, with each row's original digest, unit, declaration and executable identity.
The final file-handle unit remains separately pinned; sharing its module name is
insufficient. Every newly captured unit must have empty action inventories.
Previously admitted units and rows cannot be overwritten or claimed as new.

The profile's explicit `:limits` also require `:max-units` and
`:max-declarations`. Unit counts cover the combined baseline/current unit maps.
The declaration bound covers the aggregate entries in both baseline/current
executable maps and all four admission registries, counted before traversal; it
also separately bounds aggregate declaration occurrences across new units.
These are aggregate bounds, rather than a fresh allowance for every unit. For
example, a baseline with 334,750 executable functions needs a declaration bound
above 669,500 even before its admission entries are counted. These limits grant
no additional source authority.

The publication wrapper owns the actual `resident-source/load-and-publish` call
and captures its full returned result before deriving private provenance. It
returns an opaque publication capability. The new preparation operation requires
that capability, compares the bounded original local CI graph with the candidate
branch (ignoring only RC), and authenticates the actual header and assembly using
existing lower operations. Native graph leaves belong to the exact immutable
Source. Preparation then privately enables one issued finalizer attempt.
Existing `prepare-source-import-over-init` retains its current behavior. Caller-supplied snapshots, unit digests, descriptive receipts
and opaque-looking maps are not issuance authority. No paused control can be
armed by calling evalConst out of band; no public permission setter exists.

## Proof required before execution

Capture the exact source publication entry, final-handle unit and bounded delta
of immutable admitted units, original local declaration rows, source function
identities and original checked
compilation anchor. Derive exported A name-to-guest-CI references from its actual
ModuleData. Prove that these are the same references protected by the original
compilation's checked constant map and that the corresponding Java CIs are the
original checked objects. Do not authenticate a candidate map against itself or
accept a newly projected same-shaped Java CI as the original object.

Combine this with the exact issued Init prefix, its native CI references and
original projections, borrowed Source, exact assembly/header/import order and A
module position. Reject duplicate names, subsumption, native collisions and
missing or extra values. The attempt must inherit these original registry and
anchor identities; an edited-A sibling is a separate attempt.

During a callback, retain existing evalConst witness parsing, exact sourceModule,
unit membership, IR/runtime comparison, static closure, binding identity and
initialized-global checks. Require the actual target selected view to be the
private classic view (`isExporting = false`), its exact header/imports/module order,
quotient flag and complete constant map. The selected row's actual module index
must identify assembled A. Compare the complete expected native+A references,
not just the requested constant or a subset. The primary selected source
declaration must correspond to an exported actual CI and its original checked
projection. Executable closure and boxed/IR helper names may instead be
independently authenticated members of the same unit without standalone CIs;
keep exact witness/IR/static closure and attribution checks for those helpers.
Pinned finalization adds IR extra names to `const2ModIdx`, not to the CI map.
Do not require every helper name to have a CI or count extra names as CIs.
Extension state may evolve while
these authenticated components remain the same; Environment object identity
alone is insufficient.

This proves executable/data provenance for reconstruction. It must not create a
kernel association, source import receipt, completed result or initializer
permission. Existing `finish-over-init` still performs fresh checking of every
current constant under the current policy and creates the A-only receipt only
after successful finalizer completion.

## Helper inventory and preparation

Existing `SourceModuleImport.finalizerHeader` witnesses the pinned commit,
`isModule` and requested imports. Existing kernel helpers expose the actual
checked kernel root, persistent constant map, complete CI values and quotient
state. The reconstruction proof composes these with authenticated public getters for
selected view, ordered module names and source attribution.

Pinned public accessors include `Environment.isExporting`, `header`,
`toKernelEnv` and `getModuleIdxFor?`. Header is always read from the private base;
`getModuleIdxFor?` uses the selected base. Independently captured catalogue roots
may provide these operations with authenticated transitive closures. Availability
and actual emitted ABI must be inventoried before selecting that route. The
read-only inventory pinned in the regression record found actual archived
`header`, `imports`, `allImportedModuleNames`, `getModuleIdxFor?` and
`toKernelEnv` functions. `const2ModIdx` has pinned catalogue IR but was not in
the bootstrap archive. No exact `isExporting` declaration or boxed adapter was
found in the declaration index or archive. The separately exported
[visibility witness](SOURCE_RECONSTRUCTION_WITNESS.md) supplies that predicate.
Its actual IR must be independently admitted before profile binding capture and
prefix issuance; presence of the fixture alone grants no execution permission.
If any
required component is unavailable, add a small pinned Lean witness and admit its
exported code through the normal artifact pipeline. Host slot guesses or a
fabricated missing field are not substitutes.

A full ModuleData identity walk is not required merely for symmetry if exact
selected full-map equality, checked publication provenance, private view,
header/module order and selected source index establish the bounded proof. The
implementation review must verify that minimum evidence against pinned Lean
source. Public/module-system view support remains a separate profile.

The original-publication Java projection/reference correspondence is checked using
the original publication association, rather than a fresh Java projection. Pinned `mkModuleData` in
`Lean/Environment.lean` (1858–1885) folds the private map's stage-2 values
without copying its CIs; `SourceModuleExport.exportClassic` selects that private
classic path. This supports deriving the expected guest references, but source
inspection does not replace actual reference checks. Retain the authentic
original association and
compare actual guest map references, without recomputing a fresh projection and
calling its Java object identity original. The focused tests include real checked
generated families and reject substituting a same-shaped CI at a new reference.
The candidate local graph comparison also detects changed payloads at the same
reference before the private continuation is issued.

## Ownership, budgets and failure

Branch inheritance does not add artificial owners. New protected map/root cache
owners are real guest owners and must be accounted for explicitly; an owned
getter result can transfer into the cache without an additional retain.
Cache only under the exact protected constant map, attempt, selected view/header,
source/unit and assembly identities. The cache takes ownership of actual owned
root/map getter results; repeated temporary results are released. Extension-only
updates can legitimately replace the checked kernel root while preserving the
constant map. A changed constant map cannot retain cached authority. Successful final checking
releases proof owners exactly once in its new branch. Escrow the post-release state before adoption, so adoption failure
retains accurate remaining ownership. This is an explicit successful transition,
not automatic `finally` cleanup. Failures retain exact owner packets, not guessed
cleanup.

Callback provenance helpers use the raw handler's existing shared `:invoke`
budget and failure poisoning. They must not open a fresh raw session or reset
helper fuel. Post-publication proof helpers have a separate explicit aggregate
budget. The new candidate graph/identity proof is bounded host work; existing
header parsing, encoding and assembly retain their existing independent helper
limits. The finalizer's aggregate reservation ledger starts with finalization;
there is no claim of one global budget covering source compilation and all
preparation work. At a host boundary, reserve its
entire helper bound before any effect. Account actual helper work once. Bound
preparation-time proof work explicitly as well. The finalizer starts once;
cooperative slices do not restart it.

Privately arm the exact attempt only within authenticated driver operations and
always disarm in `finally`. A completed IO result revokes reconstruction
permission before fresh checking. Failed, completed, paused, forged, unrelated
and concurrently used attempts cannot authorize callbacks. Reentrant operations
and observers must not repeat effects. On every failure retain the latest actual
child world/session, raw boundary token or IO result, proof/input/result owners
and original cause; subsequent calls rethrow the terminal failure by identity.
No rollback, source lease closure, initializer execution or implicit retry.

Host code and admitted bindings remain trusted. The candidate graph comparison
checks a public input branch before issuance. Afterwards, private continuations,
retained owners and admitted RC behavior preserve the protected state. This is
not a sandbox against reflective host mutation of private registries or heaps.

## Validation requirements and remaining acceptance gate

1. Review concrete helper ABIs and original publication reference/projection
   provenance against the explicit API and private namespace ownership.
2. Implement profile and issued single-attempt proof with positive/negative
   actual evalConst transport and staged driver tests on all three backends.
3. Reject wrong unit/row/module/IR/function/binding, edited forks, native shadows,
   changed CI refs, map extras/missing names, wrong view/header/order/quotient or
   source index, inactive tokens and failed owner retention.
4. Verify proof-cache owners, extension-only Environment evolution, helper
   reservations, source closure, observer/helper errors, finalizer IO errors,
   current-policy fresh check rejection and adoption failures without early
   associations or receipts.
5. Run one fresh genuine initializer-free macro A→B experiment; discover actual
   macro names from admitted IR. Then independently test edited-A branch/cache
   isolation with the same B source and retained old handles.

Focused tests exercise actual raw evalConst transport and real small Java kernel
checks with modeled frontend/finalizer bodies. Native export of both original and
edited macro fixtures separately confirms empty initializer action vectors.
Neither establishes genuine hosted imported-macro acceptance. Only after the
full hosted original/edit branch gates pass should that support be reported as
working. The complete JVM campaign suite is `scripts/test-runtime.clj`; the
optional LLVM bridge has its own integration suite.
