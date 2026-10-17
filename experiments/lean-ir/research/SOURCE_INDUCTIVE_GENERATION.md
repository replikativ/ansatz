# Raw source inductive and quotient admission

Review date: 2026-10-17. Native oracle is Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Native C++ comparisons used `git show 819816b2:src/kernel/inductive.cpp` and `src/kernel/quot.cpp` in the Lean checkout; installed Lean sources have the matching public declaration definitions. This note describes required work, not an implemented general generator.

The existing Java kernel already supplies ordinary mutual recursor construction and nested elimination/restoration. Its public API is principally an **imported ConstantInfo bundle validator**. Raw `Declaration.inductDecl` has only universe names, parameter count, ordered inductive names/types/constructors, and safety. It supplies neither generated metadata nor recursors. Do not treat an empty recursor array passed to the import checker as source generation.

## Concrete gaps

1. `InductiveBundleChecker.checkBundle` selects nested handling using caller-supplied `numNested`. `NestedInductiveEliminator.eliminate` also immediately returns when that metadata is zero. Raw source must always discover nesting and derive the count.
2. `InductiveChecker.run` calls `RecursorGenerator.checkAndDeclareRecursors`, which only iterates supplied recursors. An ordinary bundle with no recursors therefore does not generate them. This must remain distinct from the new source API.
3. `generateAndCheckRecursors` exists for nested auxiliary blocks, but returns only recursors; its checked working environment is not returned. `generateRecursors` hardcodes `isK=false`, relying on its nested-block caller. General generation must use `InductiveChecker`'s computed K target and return the complete family/environment.
4. `InductiveChecker` derives `numIndices` internally but declares the caller's unchanged inductive CIs. Constructor checking uses those CI metadata fields. Source admission must create fresh correctly derived headers before constructor validation. Derive mutual `isRec` and `isReflexive` from the expanded block, `numFields` from manifest constructor binders minus parameters, ordered `cidx`, `all`, and the actual nested count. Do not mutate CIs after inserting them into a persistent environment.
5. Pinned Lean checks every syntactic occurrence of a declaring inductive for uniform parameters and universe arguments **before** normalization and nested elimination (`check_uniform_ind_occs`, lines 129–165). An occurrence erased by beta reduction can otherwise escape. Reject free/metavariables and reserved `_nested` references in both constant and projection names before transformation. Java's current auxiliary names use a different predictable namespace; the source path should use the same reserved namespace policy rather than trusting generated-name collisions not to occur.
6. Pinned Lean independently verifies generated recursor computation rules preserve types (`check_recursors`, lines 820–866). Existing Java generation checks recursor types and rule field counts, not that property. Comparing imported rules to the same generator does not validate the generator independently.
7. Pinned Lean rechecks restored constructor types, recursor types and every restored rule RHS in the final environment (lines 1325–1353). Java currently checks the nested application keys after restoration, which is necessary for phantom parameters, but does not perform all those restored-term checks. All checking phases need the configured resource budget.
8. Native `declare_recursors` applies `infer_implicit(rec_ty, true)`. Java builds a telescope without an equivalent final implicit-binder inference pass. Definitional equality can hide this mismatch in import tests, but frontend elaboration observes recursor binder annotations.
9. Constructor validation must require its return head to be its declared parent, not any member of the mutual family. The narrow fix accompanying this review changes that condition in `TypeChecker.validateConstructor`; recursive *fields* still may refer to other family members.

The current lossy checking projection erases metadata and normalizes universe constructors. Guards relying on raw syntax must run on the original guest declaration, or a lossless raw projection, before that conversion. A public source API must document rejection of out-of-range guest names/indices rather than silently truncating them. This is distinct from the generator's mathematical construction.

## Minimal API and phase structure

Add a distinct `RawInductiveDeclaration` carrying only source inputs, with nested ordered type/constructor descriptors. Expose `TypeChecker.generateInductive(Env, RawInductiveDeclaration, fuel)` returning an admission result containing the new immutable `Env`, the ordered complete generated `ConstantInfo[]`, and any projection/publication provenance. Do not expose a successful result until the final validation completes. Preserve the imported-bundle API and its comparison role.

An internal raw-to-derived conversion can reuse `InductiveBundle`, but generated metadata must be owned by the kernel phase that established it. Prefer an explicit `eliminateRaw` entry point over fabricating `numNested=1` to trigger existing code. The minimal reusable refactors are:

- Separate nested discovery from the metadata-controlled import fast path.
- Split header analysis from header publication so derived metadata is installed before constructor checking.
- Expose an ordinary generation result containing checked headers, constructors, recursors and environment.
- Pass K-target into `RecursorGenerator`; infer native-compatible implicit annotations.
- Add independent computation-rule validation and final restored-term validation.

Required algorithm:

1. Validate a nonempty mutual block, universe uniqueness, parameter range, safety policy, all source names and generated-name reservations. Reject duplicate/colliding headers, constructors and recursor names. Reject unresolved variables, reserved auxiliary references and nonuniform syntactic occurrences before reductions.
2. Run nested discovery to a fixed point over the queue of original and newly copied container types. Copy **every member of a nested container's mutual family**, substitute occurrence universes and container parameters, reabstract original parameters, and continue scanning generated constructors. Record keys, original parameter context and discovery order. The number of auxiliary types is the nested count; it is not just the number of top-level container spellings.
3. Validate all expanded headers against the base environment. Derive parameter telescope, each index count and a common result universe. Derive mutual recursion/reflexivity flags from expanded constructor syntax using the pinned algorithm. Build complete expanded inductive CIs and install them only into a temporary environment.
4. Validate constructors against those headers: parameter types/positions, exact return parent and universes, index restrictions, field universes and strict positivity in safe mode. Unsafe mode skips positivity only, not the shape/type/universe obligations. Derive each constructor's index and field count; install constructors into the temporary environment.
5. Compute elimination universe, fresh recursor level parameter and K-target. Generate every motive, minor premise, major premise, recursor telescope and computation rule using `RecursorGenerator`. Generate a recursor for every member, including empty inductives and copied auxiliary types. Preserve ordering and apply implicit-binder inference. Install **all** generated recursors temporarily before checking terms that can refer mutually to them.
6. For each constructor, reproduce native `check_recursors`: build the recursor applied to parameters, all motives/minors, constructor result indices, and the constructor applied to fresh field locals. Infer its expected type; reduce it; infer the reduct's type; require definitional equality. A rule RHS having some type is insufficient because an under-applied minor remains a well-typed function. Check recursor types too.
7. With no nesting, return the checked complete ordinary family. With nesting, restore onto the original base environment: original inductives, original constructors with restored types, original `.rec` functions and every auxiliary recursor renamed `<first-original>.rec_1`, `.rec_2`, etc. Preserve derived metadata from the auxiliary checked headers, but replace `all` with original type names. Temporary auxiliary inductive and constructor CIs do **not** survive; their computational contribution survives in the additional restored recursors.
8. Check every saved nested application in the final environment under the original parameter local context. Recheck restored constructor types, recursor types and rule RHSs there. Confirm no temporary auxiliary type/constructor names remain. Check names of restored auxiliary recursors for collisions too. Return the admission result only after all phases pass.

The source API should produce its own complete family rather than retrieve a name delta from a potentially externally backed environment. A result list also supplies the publication manifest and an exact completeness oracle.

## Quotient source declaration

Add a separate `TypeChecker.generateQuotient(Env, fuel)` returning the same admission-result shape. If the checked environment already has quotient initialization enabled, return it unchanged and an empty addition list, matching pinned `add_quot` idempotence. Otherwise:

1. Validate already-checked `Eq` and its single constructor against native `check_eq_type`: required universe arity, inductive/constructor family, canonical Eq and refl types.
2. Reserve all four names before adding anything: `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`. A pre-existing name must fail, never be overwritten.
3. Generate the canonical types and kind tags in kernel code, with native level-parameter order (`u`; `u,v` for lift) and binder annotations. Existing private `expectedQuotType` is reusable for logical shape, but uses all-default binder info and is insufficient as exact frontend-facing output without adjustment.
4. Install all four into a new environment and enable quotients only in that completed result. `TypeChecker.checkConstant`'s existing per-quotient branch enables the flag one member at a time; it is not the transaction-level source operation.

`imported_kernel/validate-quot-bootstrap` already contains the checking projection of Eq requirements and can inform the Java implementation. Keep those requirements inside the trusted kernel entry point for source admission. For the guest environment, compiled Lean exposes `lean_environment_mark_quot_init`; publication can invoke it after inserting the checked four-value family. No native kernel admission call is needed.

## Guest publication

Extend the host binding to recognize scalar `Declaration.quotDecl` without first calling `m/node`. Other variants are heap constructors. The current host handler assumes every declaration is a heap reference at dispatch.

Keep the original guest declaration rooted. Reuse original guest name/type/constructor subgraphs where they are unchanged and preserve frontend metadata there. Newly generated recursor types and RHSs need a genuine Java-expression-to-guest encoder. Rebuild names, levels and expressions through compiled Lean constructor helpers or an audited equivalent that computes **Lean** cached fields. Java structural hashes cannot be copied into Lean `Expr.data`. Any generator-local free variables must have been abstracted before publication.

Do not call this an inverse of `kernel_bridge/project-expr`: that projection erases `mdata`, `letE.nondep` and some raw level structure. Preserve provenance when transforming original terms, or explicitly carry a lossless syntax sidecar for the affected generated terms. At minimum test metadata-bearing constructor types and let-bound types and report exact syntactic differences separately from kernel definitional equivalence.

The existing `imported_kernel/project-constant` is a precise schema oracle for the generated CI encoder:

| CI | Wrapper tag | Payload object fields after tag-0 payload constructor | Payload scalar bytes |
| --- | ---: | --- | --- |
| Inductive | 5 | ConstantVal, numParams, numIndices, all, ctors, numNested | isRec, isUnsafe, isReflexive |
| Constructor | 6 | ConstantVal, inductName, cidx, numParams, numFields | isUnsafe |
| Recursor | 7 | ConstantVal, all, numParams, numIndices, numMotives, numMinors, rules | isK, isUnsafe |
| Quotient | 4 | ConstantVal | QuotKind 0–3 |

Every wrapper has one payload object. ConstantVal contains name, universe-parameter list and type. Each recursor rule is a tag-0 constructor containing constructor name, field count and RHS. Lists and Nat fields use guest encodings and ownership rules; scalar bytes follow the pinned constructor layout, not a host struct.

A new compiled post-check helper can accept `env`, borrowed original `decl`, and an owned array of generated CIs, insert every CI with the existing `lean_environment_add` export, mark quotient initialization when appropriate, and call `lean_elab_environment_update_base_after_kernel_add` exactly once. This helper is publication only. Its inputs must be tied to the just-completed Java admission result. Reproject encoded CIs and compare their full checking shapes/metadata to that result before anchoring the new guest environment. Verify exact added-name set, unchanged old world, quotient flag and generated-family completeness. Neither helper nor encoder may invoke `addDeclWithoutChecking` to generate missing members.

Preserve original owned/borrowed ABI contracts: retained source references reused in generated CIs acquire the appropriate tokens; failed publication releases temporary generated roots and leaves no accepted Java/guest association. Concurrent callbacks must not see a partially inserted family.

## Decisive tests

- Raw native/Java differential generation for Bool-like enums, empty Type and Prop, Unit-like structures, Eq-like K targets, nontrivial Prop elimination restrictions, universe-polymorphic lists, indexed vectors, mutual families with different index counts, functional recursive fields, nested List/Array forms, nesting through a mutually defined container, and multi-level nesting.
- Compare exact name set, member order where observable, every metadata field, recursor universe order, binder annotations, types and computation rules. Run independent computation-type checks and actual iota reductions; type equality alone misses reduction errors.
- Negative raw declarations: wrong mutual return parent, negative fields, oversized field universes, mismatched parameters/universes, recursive indices, nonuniform occurrences erased by beta reduction, phantom nested parameter type errors, forbidden auxiliary constant/projection names, collisions with `.rec` and `.rec_1`, duplicate names/universes and unresolved variables.
- Quotient tests: canonical Eq bootstrap generates exactly four members; missing/malformed Eq fails; every name collision fails; second `quotDecl` is idempotent; lift/ind reductions compute. No partial flag publication on a failed family.
- Guest tests: encode/reproject every generated member, call generated `.rec` through hosted Lean, then run fresh source `inductive`, `structure`, a recursive definition and a theorem using the new recursor. `casesOn`, `recOn`, `noConfusion`, deriving handlers and compiler companions are elaborator-generated subsequent declarations, not members the kernel raw-inductive generator should invent.

The narrow parent-return regression and native raw-declaration oracle accompanying this note do not establish the general pipeline. Until these generation and publication obligations are implemented, descriptive raw inductive projection must continue to fail closed at admission.

## Implemented bounded source profiles

`RawInductiveGenerator` now derives complete safe ordinary/indexed/mutual
families from raw inputs, including native implicit binder annotations and
K-target metadata. Its native differential fixture covers empty Type/Prop,
enums, recursive naturals, indexed and mutual predicates, polymorphic lists,
functional recursive fields and Eq-like predicates. Original guest expression
roots survive the checking projection and are reused by the Lean constructor
encoder. Source `letE`, metadata and noncanonical level provenance are currently
rejected rather than reconstructed from a lossy Java projection.

`RawNestedInductiveGenerator` is a separate bounded experiment. It accepts one
safe, parameter-free, unindexed `Type` whose constructor fields are either the
source type itself or `Container Source`. The one container must already be
checked, nonmutual, unindexed, monomorphic and unary; its fields may only be its
parameter or itself applied uniformly to that parameter. This profile proves
there is exactly one copied auxiliary family before invoking the existing
eliminator, and verifies the discovery result against that count. The private
source descriptor's count is derived from these restrictions, not supplied by
the caller. The unrestricted source discovery API described above is still
required before accepting more general nesting.

The transformed block passes through strict ordinary generation. Restoration
preserves every generated auxiliary recursor, followed by strict final bundle
validation, restored constructor/recursor/RHS typing, saved nested-application
typing and rejection of escaping auxiliary names. Each fully applied auxiliary
recursor computation is also closed over its local telescope, restored, and
checked for equal lhs/reduct types and definitional equality in the final
original environment. Native differential tests include a list-like container,
an empty container and a source with both direct and nested recursion; they
compare all generated CIs including the restored `.rec_1`.

Guest admission requires explicit `:allow-nested? true` plus a separate bounded
publication helper. Selection uses syntactic discovery, never catching an
ordinary checking failure and retrying another mode. Unsupported parameters,
universes, indices, mutual source families, multiple containers, higher-order
container fields and deeper nesting fail closed. This is not general Lean
source-nesting coverage. The ordinary publication helper remains separate and
continues rejecting nested families.
