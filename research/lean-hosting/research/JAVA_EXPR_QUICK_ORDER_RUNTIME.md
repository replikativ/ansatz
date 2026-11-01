# Original Expr quick ordering

`Lean.Expr.quickLt` (`lean_expr_quick_lt`, intrinsic539) implements the pinned
Lean4.33.1 source algorithm as an atomic, read-only query. The exact raw ABI has
two borrowed object arguments and a UInt8 result. Its original owning boxed
wrapper remains guest code. Raw root, PAP, imported closure, makeClosure and
Host-reply closure admission reject the borrowed native; a source FAP can borrow
its caller's operands. No constructor policy, guest callback, alias substitution,
pointer ordering or new initialized state is introduced.

This is the source relation, including its partial cases. Expr ordering checks
identity, kind, unsigned low32 cached hash and independent semantic Eqv before
selecting a child. Lambda/forall names and BinderInfo are ignored. Let nondep
precedes its type/value/body. Projections compare child, structure name and index.
Level ordering compares depth before kind/hash and structural children. Name
components are prefix-first, with numeric components before string components.
Valid Unicode scalar comparison implements valid UTF8 byte ordering without
normalizing text.

Metadata uses ordered raw KVMap entries. A pair compares Name keys and then
DataValue contents. Int and Syntax have no native less-than implementation; they
are incomparable within their kinds. Both pair directions must be tested before
continuing the metadata list. Independent equality, rather than absence of LT
in both directions, decides whether App, MData and Proj may compare their next
selector. Consequently an incomparable first selector does not permit falling
through to a later field. The implementation does not impose a new total order.

An invocation-local typed stack and identity-keyed memo avoid Java-recursive
traversal. Outer entries, including live Name component vectors, are capped at
100,000. Each fresh synchronous equality probe reserves up to 200,000 additional
entries, giving a conservative 300,000 combined entry cap. This is not a byte
cap. String lengths and Nat limb work are separately charged before temporary
work. One shared million-unit counter covers the outer traversal and fresh
probes, including failures; interruption is checked periodically. Probe maps are
not retained between comparisons. Nothing is saved in guest metadata or Program.
Atomic queries can fork before or after execution, not midway through a query.

Inputs must satisfy the existing source-valid Expr/Level/Name/metadata layouts,
valid Unicode and acyclic traversal domain. Unsafe forged shapes can reject
before a native shortcut. Nominal AST provenance, native heartbeat counts,
temporary reference-count traffic, arbitrary cyclic data and universal native
allocation parity are not claimed. The operation does not mutate guest fields,
reference counts or counters.

The [fixture](../test/fixtures/java-expr-quick-order-runtime/README.md) contains
the two exact raw/boxed rows. Four original hook rows are source evidence for
existing typed decoders, not additional guest calls or authorized aliases.
There are no initialized dependencies. Tests distinguish genuine constructor
results from forced-cache structural models. A separate safe native oracle
covers genuine metadata hash collisions and incomparable-selector behavior.

The source checkpoint is SHA-256
`938b09e4aa57109b9941d15f75e80c66dc40dedd7dcbbbe06dafe421c607baf5`;
the immutable Java11 jar is
`825c1f272b7f40eb72178f0a249963c4b8950e9864de584695d7828d4bf173e0`.
Bounded javac/jar compilation used a 192 MiB heap. Independent source review
cleared this checkpoint for focused testing. Parent retained JVM gates passed
seven semantic tests / 47 assertions and five control tests / 32 assertions in
each driver: 24 executions / 158 assertions total. The pinned native `--run`
oracle matched all 25 expected lines, exit0 and empty stderr; its receipt is in
the fixture. Native observations remain distinct from forced-cache JVM models
and control tests. The author ran no interpreter JVM or native tool. Full
combined integration and actual frontend completion remain separate gates.
