# Private Expr replacement and beta machinery

This stage implements private iterative lift, substitution and beta jobs in the
Java research interpreter. The original `lean_instantiate_expr_mvars` remains
unregistered. There is no Expr context traversal, direct/delayed assignment
resolution, embedded Level session or new public invocation API in this unit.

The reflection-only `startExprMachineryResearch` driver is private and explicitly
research-only. It admits owned input/vector occurrences at an open idle active
explicit boundary after validating mode/bounds, actual source Headers and known
alias credits. It starts a null-Function action with an OBJ result; `takeResult`
now agrees with `finishAction` when that private action has no Function. Ordinary
nonnull scalar-root result handling is tested separately. Production jobs borrow
inputs backed by their caller's owners; this driver is their bounded test caller.

Nine immutable exact constructor roles bind original Names, raw SHAs, canonical
bodyless declarations, parameter IDs/borrow flags and one SourceBinding. The
current Program Functions must remain ordinary, non-host, non-intrinsic and
unredirected. Source byte authentication belongs to the trusted loader; the
policy does not prove it from descriptive hashes. Constructor bodies may be
unprepared and suspend through ordinary CodeRequest. Lam/forallE/letE use the
actual owned boxed wrappers; they receive tagged BinderInfo/Bool values.

Replacement uses a typed iterative frame stack and an independent cache for each
job, keyed by Expr identity and binder offset. The native `replace_rec_fn`
heuristic samples `rc != 1` before replacement effects, so MT count-one Exprs
remain likely unshared. This differs deliberately from the Level instantiator's
`!exclusive` test. Cache hits skip children; unchanged updates return the original
pointer. Applications visit function then argument, binders domain then body at
offset+1, and lets type/value then body at offset+1. Metadata payloads and binder
names/flags survive rebuilding.

Lift prunes by the cached loose-bvar range and handles cutoff/amount zero without
traversing. Substitution uses the native non-reverse vector: below binder offset
stays unchanged; a substituted argument is lifted by that offset; later indices
shift down by the vector length. Nat arithmetic stays arbitrary precision until
a bounded constructor/vector index is established. No forged large index is
silently narrowed. Constructors supply exact hash/range/depth/flag data.

Beta follows `apply_beta_rec`, with reverse arguments, partial/overapplication,
zeta and head-only metadata stripping. Zero arguments preserve the exact input.
Each recursive by-value Expr parameter remains owned until the inner result
returns, and `apply_beta`'s separate wrapper owner survives the recursion. A
borrowed lambda/MData child receives a new parameter credit. A zeta replacement
prvalue moves into its child frame under the pinned C++20 profile. Non-lambda
application retains both the instantiate full-expression temporary and a separate
accumulator; each old accumulator releases after its new App result exists.
Cleanup drains recursive owners deepest-first, then the wrapper.

Constructor packets own acquired occurrences until actual frame/CodeRequest
publication. The existing entry protocol matches Function and original argument
array before transferring flags, including frame publication before tick failure.
Returned values are owned in the receiver slot before validation. Wrong results,
interruption and failures retain their exact packet/control graph. Each release
stages cursor, retiring owner and claim disposition before the existing resumable
release continuation; no successful failed-engine unwind is claimed.

One identity memo forks frames, input/result/temporary credits, packets and cached
keys/values, preserving occurrence aliases and independently copying mutable job
state. Immutable policy is shared. Stage one leaves the standalone Level algorithm
unchanged; only the shared helper-entry hook delegates to the appropriate current
typed packet. No Node fields, semantic cache words or kernel classes are added.

The profile bounds aggregate work to one million units, live frames and cache
reservations to 100,000, and cutoff/amount/offset to 1,048,575. The maximum rebuilt
bvar index is 1,048,574, matching the original 20-bit range constructor boundary.
Reservations survive until each job's entire cache drain completes. Interruption
checks are cooperative. These bounds are host policy, not native heartbeats or
allocation parity. Supported semantic inputs are acyclic source-produced Exprs
with consistent cached words. Fast paths do not certify every reachable node;
encountered malformed structural cycles and forged out-of-domain caches reject.

The [fixture](../test/fixtures/java-expr-machinery-runtime/README.md) pins original
roles and source. Models identify their own scope. No native oracle, image restore,
full frontend success or ExprMVars implementation is claimed by this stage.

## Verified stage-one validation

The parent campaign's retained 384 MiB JVM passed the final private research
suite: 20 tests / 165 assertions, zero failures or errors. Frozen Java source:
`73be76e7517211cd39272ff6251cb6ec835755579c40bc1e41b0af2078268cbc`.
Immutable Java 11 jar:
`ba10588e3b7ec325f38eacf3b60d24198d7e79ab9839cdfad903cec4b114bd02`.
The final test file is
`ad2f6f8b78cbe4e904dd539bef73c972028ff68dc02ce69002ce39ad2074459e`.
The flat parent receipt is
`target/java-expr-machinery-integration-v1/focused-final-v3.out`.

An earlier 1,000-binder case exhausted a generic test helper's 100,000 single-step
host-call limit. The private research finisher now batches at most 64 dispatches
only in RUNNING phase, with independent two-million-dispatch / 30-second bounds
and explicit boundary diagnostics. The deep case passes without unexpected Code
or Host demand. Production work/frame/cache limits and source semantics were
unchanged; dedicated suspension/fork tests still single-step.

Astra independently reviewed the source, owner stack, aggregate reservations,
fixtures and final semantic/control tests. This worker ran bounded Java 11
compilation, source/CAS/index hashing, delimiter and path audits and
`git diff --check`; it launched no JVM test runner or native oracle. The combined
integration regression gate is separate parent evidence.


The combined integration with the landed level substitution, checked-array and
expression-search runtime passed the complete regression runner at a 384 MiB
heap limit: 115 test families, 1,139 test executions and 54,111 assertions, with
zero failures or errors. Integrated Java source SHA-256:
`d9999cf8a442d5de163408d00dc34c3f095c79e028f8f21c7c8b960a6315590a`.
Immutable Java 11 jar SHA-256:
`9c4f30f0068cfd0891e1c071a3762ac41713112c7a51d0ca14b4d470445a8123`.
The campaign receipt is `target/java-expr-machinery-integration-v1/combined-gate-v3.out`
(SHA-256 `046fb2e2e8ebf91b51e7719d162ae9cfbbf691e3b9f990a108c4272f7ff58a8a`).
An earlier retained-REPL search fixture run failed before execution because of a
relative fixture path; the corrected absolute-path run passed all 10 tests and
106 assertions on this same artifact. These are JVM regression results, not a
native differential oracle or a new frontend compatibility claim.
