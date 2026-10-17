# Borrowed expression ordering

The ordinary-file probe reached the previously unsupported
`Lean.Expr.quickLt` / `lean_expr_quick_lt` after full Init finalization and strict
kernel association. The implementation in
[runtime_expr.cljc](../src/prototype/runtime_expr.cljc) now provides that primitive
and its structural counterpart, `lean_expr_lt`. Both borrow two guest Expr
objects and return UInt8 Bool without changing the world or reference counts.
They operate directly on guest constructor layouts; neither native execution nor
Java kernel projection is used by the hosted runtime.

The source reference is Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, not the sibling checkout's working
tree. Relevant pinned paths are `src/library/expr_lt.cpp`,
`src/kernel/level.cpp`, `src/kernel/expr_eq_fn.cpp`, `src/util/name.cpp`,
`src/util/kvmap.cpp`, `src/runtime/list_ref.h`, and `src/runtime/pair_ref.h`.
The installed `Lean/Expr.lean` declares the borrowed externs. Exact signatures
are registered in [runtime_signatures.edn](../src/prototype/runtime_signatures.edn).

The comparison rules matter beyond ordinary lexicographic traversal:

- Expr kind is compared first. `quickLt` then compares the unsigned low 32 bits
  of the cached hash; `lt` omits this hash comparison. Structural Expr equality
  and constructor-specific tie-breaks follow. Cached depth and occurrence flags
  do not become additional Expr ordering keys.
- Universe Levels compare cached depth before kind, then hash when enabled,
  then structural tie-breaks. Level lists select the tail only when their heads
  are structurally equal. This is not normalized universe equivalence.
- Names compare prefix-first components, with numeric components before string
  components. Name hashes do not determine their order. Nat components and
  literals use contextual native-scalar/MPZ reads; strings use UTF-8 byte order.
- Lambda/forall binder names and binder information do not affect this ordering.
  Let names are ignored, but let nondep flags participate before type, value,
  and body comparisons. Projections compare body, structure name, then index.
- Pinned metadata ordering has a deliberate corner: same-kind DataValue Int and
  Syntax comparisons return false in both directions. The implementation keeps
  that behavior rather than inventing an order. A metadata list can therefore
  continue to later entries after incomparable values. In contrast, an App with
  structurally unequal functions returns its function comparison immediately;
  it must not proceed to its argument merely because both function directions
  were false. The native matrix exercises this distinction.

The comparator uses an explicit work stack and invocation-local structural
equality memoization. It retains no memo across worlds, environments, forks, or
calls. Traversed cycles and malformed layouts fail explicitly. Normal Exprs are
expected to have consistent computed caches. The oracle deliberately forces
collisions to exercise structural fallbacks, but this is not a claim of complete
compatibility with arbitrary forged inconsistent computed fields. In particular,
native expression equality has an app-spine optimization that can differ from a
generic recursive equality walk only on such inconsistent intermediate caches.
Native heartbeat charging inside comparison remains unmodeled.

The [native oracle](../native/ExprOrderOracle.c) calls both symbols in the pinned
Lean shared library directly. Its
[fixture](../fixtures/expr-order-native.json) contains 65 named expressions and
all 4,225 ordered pairs: 8,450 native comparator results. Coverage includes all
12 Expr constructors and all six DataValue constructors, colliding hashes,
high hash bits, binder equivalence, level order, hierarchical numeric names,
large Nat objects, UTF-8 order, metadata incomparability, and projection fields.
The fixture SHA256 is
`7461e7415d05cc5deaf016a287b2a4cae00d81608ecf04ca37e1d0b22228ae98`.

[Focused tests](../test/prototype/runtime_expr_order_test.clj) compare the full
matrix and verify borrowed-world identity. They exercise actual ABI lowering
across reference, mutable, demand JVM, and eager JVM execution at budgets
0/1/2/3, including cold/hot demand dispatch. Separate tests cover 3,000 nested
collisions, traversed cycles, malformed arity, and ownership-signature rejection.
Together with the existing Expr and ABI suites, validation passed 18 tests and
17,905 assertions with zero failures or errors in one guarded 256 MiB JVM.

The consolidated [measurement](../measurements/runtime-expr-order.json) records
the final 65-case native run and focused JVM guard observations. The native
compile/oracle stages and focused JVM ran serially. All completed without
crossing the 1 GiB available-memory floor; the corresponding start threshold was
1.5 GiB. RSS observations were sampled every 250 ms and do not establish an
exact peak, especially for the brief native oracle. Earlier 55-case native
metrics must not be attributed to this expanded fixture.

Live adoption is separate from fixture generation. It requires publishing the
two supported-symbol entries and signature delta, lowering only the actual
deferred `quickLt` declaration, and matching the resulting function table to its
session and trusted evalConst capability. There are no new runtime namespace
aliases, imports, helper dependencies, or initializer actions. This note records
comparator validation; it does not claim the ordinary-file probe has completed.
