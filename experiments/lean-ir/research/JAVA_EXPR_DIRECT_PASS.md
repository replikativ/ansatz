# Private direct Expr assignment pass

This stage implements the complete **first/direct pass** of pinned Lean's
`instantiate_expr_mvars` as a private research action. The original
`lean_instantiate_expr_mvars` extern remains unavailable. A private reflection-only
entry produces a research ctor0 `[currentContext, directExpr, delayedFlag]`;
this is neither the native result ABI nor a finished Expr instantiator. Delayed
assignment substitution, resolver generation caches and the second pass remain
outside this unit. No frontend acceptance or native heartbeat parity follows
from these private jobs.

The algorithm reads ordinary guest Expr/Level/context values. It adds no Node
fields, nominal AST identity or Java kernel storage. Shape checks use existing
constructor layouts and cached data flags; they are not whole-graph or nominal
certification. Input builders and malformed cases in the tests are identified as
models separately from authenticated original helper rows.

## Source and helper contract

The semantic source is Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, especially
`src/library/instantiate_mvars.cpp`, `src/kernel/replace_fn.h`,
`src/runtime/option_ref.h`, `src/runtime/list_ref.h` and
`src/runtime/buffer.h`. The fixture pins source-file hashes and accepted original
CAS/index identities. Nineteen canonical ordinary helper roles comprise the
existing five Level helpers, nine Expr constructors, and these five functions:

- `Lean.MetavarContext.getExprAssignmentExp`
- `Lean.MetavarContext.getDelayedMVarAssignmentExp`
- `Lean.DelayedMetavarAssignment.fvarsExp`
- `Lean.DelayedMetavarAssignment.mvarIdPendingExp`
- `Lean.assignExp`

The fvars accessor is mandatory configuration evidence but is never called by the
direct pass. Every role requires its exact typed Name, raw ABI and borrow flags,
source binding, ordinary declaration metadata and current actual Program Function
identity. Guest-export/native/Host substitutions of these roles are rejected.
Missing bodies are permitted and use existing CodeRequest continuations. Raw
hashes are descriptive policy pins: the trusted research loader authenticates raw
bytes; a caller-created matching hash string is not source authentication.

The private entry requires an open, idle, active explicit engine, all installed
helper headers and known owned-input alias credits before publishing any owners.
There is no new public native or invocation hook. Both configured context and Expr
input are consumed once. Construction delegates the existing private typed Expr
constructor protocol; it does not duplicate its algorithms or synthesize a guest
function.

## Traversal and source lifetimes

A single MVarContextCell owns the current context; getter packets copy it and
setters steal it until their validated return. The existing reusable LevelSession
and private replace/lift/substitution/beta workers share one InstantiationBudget.
No nested root start or counter reset occurs. Only one direct-helper, constructor
or Level packet can be outstanding. Entry commits match the current action,
actual Function and original packet-array identity at Code publication/frame
publication before tick. Receivers own results before validation; malformed
returns keep their owned receiver and remaining continuation packet.

Expr flags select the no-mvars fast path. Shared composite caching samples
`!exclusive`, including logical MT, before traversal retains. The nested replacement
worker keeps its distinct native `rc != 1` likely-sharing heuristic, regardless
of logical MT. MVars are never
cached. Normalized assignment Names use owned keys with semantic Name equality,
so distinct but equal Names stop direct cycles. There is no raw active-Expr cycle
exception before this semantic cutoff: valid assignment reentry can revisit a
composite. Duplicate cache insertion keeps the first cached value while returning
the newly computed result, including a separately escrowed attempted-insert copy.
Malformed structural cycles and excessive work fail named host profile bounds;
identity/fast-path shortcuts do not certify all reachable storage.

Assignments retain both the getter Option and its extracted assignment local.
Changed assignments save the old assignment before the setter can replace the
context map. The delayed probe holds an Option, a separate record temporary
because `option_ref::get_val()` returns by value, and the accessor's owned packet
occurrence. The record temporary drains only after the pending Name returns.
The pending Name and condition-result Expr retire before unresolved App fallback;
the delayed Option stays alive throughout that fallback. `delayedFlag` reports an
assigned pending Name only; it does not resolve the delayed assignment.

Apps visit arguments outermost first for assigned-head beta; their buffer owns
returned arguments through the borrowed beta vector. Ordinary non-MVar function
spines bypass the outer visitor cache as in C++. The existing beta worker keeps
its wrapper and recursive by-value ancestor owners, zeta moved child and separate
full-expression temporary/accumulator. Inner App temporaries retire before outer
cache insertion. Ordinary binder/mdata/proj/Sort/Const temporaries survive that
insertion. Metadata, binder annotations and nondependent-let flags are preserved
by original constructor bodies.

Const Level lists use native tail-first `map_reuse` order. Unchanged suffixes keep
identity, and the first changed head stays owned through the whole prefix build.
Prefix cons construction has explicit head/tail loan and partial-shell escrow.
There is no extra retain merely to start a borrowed Level job. Saved assignments
and caches persist across all Level jobs, sharing the latest context cell.

At direct completion, raw Expr/Level keys detach while anchors are still live.
The original input retires at the native first-pass semicolon boundary. The
private report acquires its own Expr occurrence and current context, and remains
unpublished while Expr saved values, cache values, normalized Names, then Level
saved/cache values drain. Every release records its stage and exact owner before
resumable release can demand Code/Host work. Fork copies state, credits, keys,
packets, receiver aliases, cell, budget and mutable collections through one memo;
immutable policies and Program metadata remain shared.

Work, frame, cache, saved-value, Name, argument-buffer and Level-list limits are
explicit host profile guards, not an aggregate heap cap or native heartbeats.
Synchronous read-only equality imports/exports shared work in `finally`. Failure
keeps exact remaining owned slots; no successful failed-engine unwind or universal
C++ temporary destruction/callback trace equivalence is claimed.

## Validation

The focused suite is active-explicit only and distinguishes authentic helper
execution, labeled storage/body adapters and forged-domain failures. The finite
fixture contains twenty root rows (nineteen roles plus native-negative evidence)
and 111 rows in their exact FAP/PAP helper closure, with no initialized dependency.
It does not import a frontend image or export a whole compiler catalogue.

Source review, focused observations and combined-gate results are recorded when
available. The author uses bounded Java 11 compilation and metadata/file audits;
all JVM execution is performed by the parent in its retained bounded REPL.

Astra's independent source/fixture review cleared activated source
`1c3bc2001f975f4c53721862a0d9f863bbf2f9372e1fff0c2e36f2eedab8eebd`
and the twenty-one focused cases for parent execution. The author compiled that
source with Java 11 / 256 MiB to immutable jar
`85995f8cf32182d7fd269a2d1d2c3ee93779cf7f2667d776a470b39ae447331a`.
Direct-specific frame-entry tick failures and failure/fork during final member
drain are not yet covered by this matrix; existing shared continuation tests are
not presented as exhaustive direct-pass terminal cleanup evidence. Any eventual
native activation needs its own complete two-pass and failure-path acceptance.

The parent retained 384 MiB JVM passed the final focused suite: **21 tests / 169
assertions**, zero failures/errors, on that unchanged source/jar. The same
artifact also passed existing Level20/310, private Expr machinery20/165 and
shared-session11/148 regressions. Final direct test SHA is
`d88a3b501c858137b006f650673008343de0045a300a199de543dfc160eabbb1`.
Parent receipt `target/java-expr-direct-integration-v1/focused-v4.out` has SHA
`af1e3b988bdbf43c31989f83733bb8dc1681fa21678487fcd183cc34a8a7450b`.

Initial focused failures were test assumptions: a pause predicate used `code`
instead of the actual `code-call`; an App-function spine bypasses normal cache
lookup, so the cache-hit model now uses shared binder domain/body; and the
inactive-entry model originally attempted active-only helper configuration before
reaching its intended entry rejection. Correcting those fixtures/predicates did
not change the compiled artifact, dispatch/work limits or runtime semantics.
The runner adds one active-explicit21-test group; the combined integration gate is
separate evidence still required after source integration.

The pass is now integrated with the original replacement/abstraction natives on
base `39dbcfe2fa9ce4bcc8107314e861f2c8b89f3c6e`. Independent source review
confirmed the action-ID and same-memo fork unions preserve both implementations.
Integrated Java SHA-256 is
`6c836542017fd297d235c3a4d56a1e3c51e75f72973457c9695839b1d3003f5d`;
immutable jar SHA-256 is
`60eea1e1be6b0295dcb425a294ebe00e82d838c143ad854226ec2f0960d029b0`.
The retained REPL passed direct21/169, replacement18/240 and abstraction19/168
on that same artifact. The separate 384 MiB combined gate exited zero:
**121 groups / 1,228 tests / 55,012 assertions**, with no failures or errors.
The initial gate launch lacked the documented TypedLongMemo classpath helper
and stopped before tests; compiling that unchanged helper fixed the harness.
The original Expr native remains unavailable pending the complete second pass.
