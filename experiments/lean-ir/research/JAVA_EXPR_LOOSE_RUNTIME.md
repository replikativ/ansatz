# Expr loose-variable search and lowering

This pair implements original `Lean.Expr.hasLooseBVar` (intrinsic 537) and
`Lean.Expr.lowerLooseBVars` (538), pinned to Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. `quickLt` is a separate unit and is
not recognized by this change. Both raw natives borrow every argument. Their
unchanged original owned boxed wrappers remain supported; raw root, PAP,
makeClosure, imported closure and Host-reply closure admission retain the five
borrowed-native fences.

Search is an atomic read-only operation in either driver. It validates the live
Expr and canonical logical Nat carrier, returns false for canonical heap Nats,
and narrows immediate search indices to unsigned32. Thus 2^32 searches index0
and 2^32+1 searches index1. Exact immutable small BigInteger inputs follow the
same typed mathematical Nat domain as Long; this does not reconstruct a native
noncanonical small-MPZ allocation history. Negative and wrong-class inputs reject.

An invocation-local iterative stack tracks Expr identity and binder offset. The
native likely-unshared hint is exactly `rc == 1`, including logical MT at RC1.
Const/BVar/Sort bypass the visited cache. Other shared entries consult/insert the
identity-plus-offset key before evaluating the predicate. The predicate handles
unsigned32 index/offset overflow and cached-range pruning before comparing exact
BVar indices. App function precedes argument, binder domain precedes body at
incremented offset, and let type/value precede its incremented body. Metadata,
names, levels and annotations are not searched; partial Apps are visited.

A match returns immediately because the source's remaining predicate calls have
no guest effects. No guest retain/release, cached-word mutation, constructor or
callback occurs. Temporary search state never enters Program, Node metadata,
runtime failure records or fork state. Work is capped at one million units,
visited keys and scratch stack at 100,000 entries, and offset at the existing
1,048,575 ceiling, with periodic interruption checks. Encountered active cycles
reject; pruned/identity shortcuts do not certify unvisited graphs. Immediate
children are shape-validated while enqueued, which can reject malformed hidden
storage earlier than the native visitor. This is an unsafe-domain distinction,
not a source-produced semantic change. Native heartbeat/work counts are not
claimed.

Lowering extends the existing offset replacement worker with mode5, the same
immutable nine-constructor `ExprTransformPolicy`, action18, typed owner packets,
cache draining and same-memo fork. It requires active explicit configuration even
for identity cases. It first validates both canonical Nats. A heap parameter or
full-width immediate s<d returns an owned copy of the input. Only then do s and d
narrow to unsigned32; d32==0 and s32>=cached range retain identity. A continued
s32<d32 rejects before primitive ownership publication. That is a declared
rejection of the pinned debug-assertion domain; assertion-disabled native builds
may behave differently. It does not silently clamp or use a Lean source fallback.

For a selected BVar, lowering requests the authentic original constructor for
index−d32. It preserves offset pruning, likely-unshared `rc != 1` cache semantics,
left-to-right children, unchanged-child identity reuse, scalar flags and all
non-Expr fields. The original constructor recomputes cached data. Raw input is
borrowed from its parked caller without an extra root retain; the result owns its
credit. Existing lift, substitution, beta, abstract and callback-replacement
modes retain their earlier behavior. Source-valid Exprs and cached range words
are required; malformed/overflow model failures retain actual packet owners and
claim no general failed-session unwinding.

The [fixture](../test/fixtures/java-expr-loose-runtime/README.md) contains four
exact raw/boxed rows and a 55-row static constructor-helper closure with zero
initialized declarations. It is a subset of the separately researched 75-row
three-native envelope. This metadata adds no required initialized heap root and
is not source, kernel, or heap-admission authority.

Parent retained JVM first gates passed eleven tests / 76 assertions in each driver
on source SHA-256
`fd7bea79adf3bf4f93c32e6ddefb24cc0e863aaf5e59c2efc3c63a680b2076a7`,
immutable Java11 jar SHA-256
`697fda825983ae551f12bb7d5804797ebbf3e7507273473db99acda8cad7cb71`.
Only the query uses the selected driver in these runs; lowering is deliberately
active explicit in both. Five resource/control tests also passed 40 assertions in each driver, and two
active-explicit admission tests passed 18 assertions. Total: 34 executions /
250 assertions. The safe seventeen-line native oracle excludes the continued narrowed
assertion domain. Its first attempt failed parsing a reserved local identifier;
no native case ran in that attempt. The corrected source then matched all seventeen expected lines in parent pinned
`--run`, exit 0 and empty stderr. This observed receipt remains distinct from JVM
results. No author interpreter JVM or native tool
ran; bounded javac/jar used a 192 MiB heap. Full combined integration and actual
frontend completion remain separate gates.
