# Original FindExt declarations

These are the exact raw and owned boxed declarations for `Lean.Expr.findExtImpl?` from accepted producer index `74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`. Original raw CAS hashes are retained per record; only optional top-level `pretty` was removed. `provenance.json` pins the transformed fixture and Lean 4.33.1 source hashes. Upstream source is Apache 2.0; see `LICENSE`.

The raw native ABI takes two borrowed objects (predicate, Expr) and returns owned `tobject`. The original boxed wrapper owns its inputs and runs its original decrements. There are no initialized dependencies. This is authentic source/ABI evidence, not a record of native callback execution.

`FindExpr.lean` defines FindStep as found=0, visit=1, done=2. Native `for_each_fn<false>` skips intermediate function-spine applications and their cache entries; ordinary `for_each_fn<true>` Find visits those applications. Both use the dynamic likely-unshared hint and the same source child order. The Java unit preserves this distinction.
