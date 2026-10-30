# Original Expr.find runtime evidence

Pinned Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (4.33.1).
Accepted original IR index: `74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`.

`original-rows.json` retains 19 authentic original CAS declarations: `findImpl?`,
its owned boxed wrapper, ordinary `find?` and `hasSorry`, their wrappers and
closed static dependencies. Only optional top-level `pretty` is omitted; the
stored SHA for each row identifies its complete original CAS bytes, including
that field. Source and normalized fixture hashes are in `provenance.json`.
There are no initialized global dependencies in this selected static closure.
The inherited source association of a caller's Expr graph remains separate.
Upstream code is Apache-2.0; see `LICENSE` and source headers.

The native ABI of `lean_find_expr` borrows both predicate and Expr, returning an
owned Option. The original boxed wrapper owns its arguments and is the supported
first-class/root route. This fixture does not admit `lean_find_ext_expr`, whose
FindStep callback and partial-application policy differ.

The focused JVM suite mixes genuine original wrappers/constructors with labeled
IR and private control models. Those models exercise traversal, sharing hints,
callback/code/host pauses, forks, escrow, limits and failure states; they are not
claimed to be native-produced well-typed Expr graphs. The work-limit and overflow
models deliberately change private state. No separate native find oracle was run
for this fixture; pinned C++ and original IR are its semantic evidence.
