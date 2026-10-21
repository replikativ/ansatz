# Scoped source reconstruction during import finalization

This is an implementation proposal and focused regression contract. It grants no
new execution permission. The current completed-import profile still requires
an actual checked target association and its completed source import receipt.
The [regression record](../measurements/source-reconstruction-ordering.json)
records **892 tests / 90,162 assertions**, plus focused controls on all three
backends and an ordinary-classpath runner load. It distinguishes source-derived ordering from actual hosted frontend evidence.

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
constant values, before its final IO result. Current source authorization rejects
that transition and preserves the terminal checkpoint/session without replay.
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
the proposed reconstruction profile. Future import fixtures should root functions
such as `Nat → Nat` and `String → String`, and inspect their actual action vectors.

## Proposed public boundary

Keep the first implementation in the existing optional
`prototype.resident-init-prefix` namespace unless review finds a cleaner ownership
boundary. That keeps its private prefix certificate, issued operation registry,
active reconstruction token and cooperative driver together. No public generic
arming function, certificate getter or caller-supplied proof map is proposed.
The following names and argument shapes are proposals, not available APIs:

```clojure
;; Before preparing the independent native configuration and issuing its prefix:
(prepare-reconstruction-profile exporter eval-options helper-configuration)
;; => {:profile opaque-profile :eval-binding exact-host-created-binding}

;; After admitting that binding in a distinct independently captured profile:
(prepare-source-reconstruction-import-over-init
  context request issued-prefix opaque-profile options)
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

The explicit new preparation operation authenticates the actual header and
assembly using existing lower operations, then privately issues a capability for
one finalizer attempt. Existing `prepare-source-import-over-init` retains its
current behavior. Caller-supplied snapshots, unit digests, descriptive receipts
and opaque-looking maps are not issuance authority. No paused control can be
armed by calling evalConst out of band; no public permission setter exists.

## Proof required before execution

Capture the exact source publication entry, immutable admitted unit object,
original local declaration rows, source function identities and original checked
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

## Helper inventory and unresolved decisions

Existing `SourceModuleImport.finalizerHeader` witnesses the pinned commit,
`isModule` and requested imports. Existing kernel helpers expose the actual
checked kernel root, persistent constant map, complete CI values and quotient
state. They do not currently provide one reconstruction-view witness covering
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
found in the declaration index or archive. A distinct witness for that predicate
is therefore still required; this regression PR does not supply or admit it.
If any
required component is unavailable, add a small pinned Lean witness and admit its
exported code through the normal artifact pipeline. Host slot guesses or a
fabricated missing field are not substitutes.

A full ModuleData identity walk is not required merely for symmetry if exact
selected full-map equality, checked publication provenance, private view,
header/module order and selected source index establish the bounded proof. The
implementation review must verify that minimum evidence against pinned Lean
source. Public/module-system view support remains a separate profile.

The original-publication Java projection/reference correspondence also needs a
specific implementation review. Pinned `mkModuleData` in
`Lean/Environment.lean` (1858–1885) folds the private map's stage-2 values
without copying its CIs; `SourceModuleExport.exportClassic` selects that private
classic path. This supports deriving the expected guest references, but source
inspection does not replace actual reference checks. Retain the authentic
original association and
compare actual guest map references, without recomputing a fresh projection and
calling its Java object identity original. This PR deliberately introduces no
partial authority implementation while those helper/provenance choices remain
unresolved.

## Ownership, budgets and failure

Branch inheritance does not add artificial owners. New protected map/root cache
owners are genuine additional proof owners and must be retained explicitly.
Cache only under the exact immutable map/root, attempt, selected view/header,
source/unit and assembly identities; a uniquely mutated map cannot retain cached
authority. Successful final checking releases proof owners exactly once in its
new branch. Escrow the post-release state before adoption, so adoption failure
retains accurate remaining ownership. This is an explicit successful transition,
not automatic `finally` cleanup. Failures retain exact owner packets, not guessed
cleanup.

Use the existing outer/helper/aggregate reservation policy. Additional provenance
helper calls must be bounded and charged to the same attempt; do not hide
unbounded guest work inside host authorization. At a host boundary, reserve its
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

## Follow-up implementation gates

1. Review concrete helper ABIs and original publication reference/projection
   provenance; settle the proposed API and private namespace ownership.
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

Only after those gates pass should imported macro support be reported as working.
