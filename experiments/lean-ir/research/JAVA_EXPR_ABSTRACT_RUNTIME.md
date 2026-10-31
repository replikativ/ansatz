# Original Expr abstraction on the Java runtime

This bounded active-explicit profile implements original `Lean.Expr.abstractRange`
and `Lean.Expr.abstract` (`lean_expr_abstract_range` / `lean_expr_abstract`) at
intrinsics 522/523. It reuses the typed replacement, constructor CPS, result-owner,
cache-drain and fork machinery. It does not enable arbitrary callback replacement
or the full expression-metavariable native by itself.

Both raw natives borrow every input. Their unchanged owned boxed wrappers release
their inputs after receiving the owned result. Raw external roots, PAP, closure
creation, imported closures and returned raw closures retain the borrowed-native
fences. Ordinary direct FAP and owned boxed root/AP calls are supported. Configure
one immutable `ExprTransformPolicy` while idle; every native entry checks its
source cohort and all nine current ordinary constructor Functions. Source-byte
authentication belongs to the trusted loader; descriptive hashes are insufficient.
Private research entries keep their independent policies.

The implementation follows pinned Lean `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
`kernel/abstract.cpp:38–80` and the offset-aware `replace_rec_fn` in
`kernel/replace_fn.cpp`. Cached fvar, expression-mvar and universe-mvar bits all
participate in the shortcut. A zero prefix still traverses and caches when those
bits are present. Scan the live prefix backwards, matching FVar only with FVar
and MVar only with MVar using semantic Name equality. The highest matching index
wins. Bound variables already present are unchanged; a new occurrence receives
`binderOffset + prefixLength - matchedIndex - 1`. Domains precede binder bodies;
let type/value precede its body; App function precedes argument. Non-Expr fields,
constant universes, metadata, names, binder flags and let nondep are preserved.

Nonnegative Long range values clamp to the Array's live size before narrowing.
BigInteger takes the native heap-Nat full-array branch, including a small heap
Nat supplied by a host model. Negative ranges reject. Spare Array slots are never
visited. The original cached words and well-formed acyclic Expr storage are part
of the supported domain; forged words/storage are separately labeled models.

Abstraction uses `(Expr identity, binder offset)` cache keys and the native
likely-unshared heuristic `rc != 1`, which excludes logical MT at RC1. This differs
from public callback replacement's nonexclusive-node cache. Rebuild changed nodes
through authentic constructors; retain unchanged identity with a fresh owned
occurrence. Cached results own separate credits. Cache publication precedes
retirement of child locals, and raw keys clear before their backing call ends.

One native action borrows root/Array from its parked caller. Its machinery input
slot and owned argument vector stay empty; the private research root entry and
counter resets are not used. Output, constructor arguments, cache entries, child
results and retiring occurrences retain their existing explicit owner states.
Fork remaps the borrowed Array, root, prefix cursor, offset cache, helper packets
and credits through the same memo. Failure retains partial owner state and does
not imply general failed-session unwinding or finalizer completion.

Bounds reuse the aggregate one-million work budget and 100,000 frame/cache limits.
The prefix is capped at 100,000 entries. Each inspected slot and Name comparison
charges the same budget; comparison work propagates even on failure. Existing
binder/index bounds reject unsupported results instead of reproducing native
unsigned narrowing. Source C++ unsafe structural cycles have no termination
promise; this target rejects encountered constructor cycles. Native heartbeats,
all allocation/RC traces and arbitrary overflow behavior are not claimed.

The [fixture](../test/fixtures/java-expr-abstract-runtime/README.md) includes four
exact raw/boxed rows and nine constructor roles. The static helper closure has
55 rows and no initialized globals; it does not require a larger runtime image.
This metadata result alone does not establish execution coverage.

The retained 384 MiB REPL passed 19 focused tests / 168 assertions on Java source
`6c4d69841336449f5722a69617e1a82a48631129bcd7a461b65faad5fd78a6fa`.
They cover semantic domains/duplicates/ranges, all rebuilt composite forms,
zero-prefix and universe-MVar-only cache behavior, MT RC1, direct/boxed/AP calls,
borrowed fences, same/different offset cache aliases, partial-scan/constructor/
Host/live-cache forks followed by complete drains, malformed receiver escrow, structural cycles and budget
failure. The ownership-transfer refinement in the cycle model separately passed one
test / six assertions on the same artifact. The live-cache fork is not a pause
inside a partially progressed release action. The pinned native `--run` oracle matches eleven
content/identity observations. Small heap Nat and malformed storage cases are
backend models, not ordinary native producer claims. Other individual bounds and
direct interruption are not exhaustively tested. Combined integration remains a
separate gate; no original frontend theorem/definition completion follows from
these unit results.


The combined native-transform integration passed 120 groups, 1,207 executions and
54,843 assertions, zero failures/errors, exit 0 with a 384 MiB heap limit.
Integrated Java SHA-256:
`18e2d323be4f4a328a65d57e2582445531efa1a640f2245b51699e2848f70c42`;
immutable Java 11 jar SHA-256:
`0447eb5cf8fb3d2c20238d0e39f301968b2eb6971dcedfc825d52048d8c65789`;
combined output SHA-256:
`657530f318a645fcc97fc53a6f2dde6f652a23ed6339a3af3d904b8f707b7bff`.
Independent integration review verified both visitor cache policies, raw-entry
fences, source-policy checks, typed owner state and fork fields. The native
ExprMVars capability remains unavailable. These results cover the integrated
runtime; actual frontend theorem/definition completion is a separate gate.
