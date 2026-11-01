# Original callback Expr.replace fixture

Exact accepted-index declarations for `Lean.Expr.replaceImpl` and its unchanged owning `_boxed` wrapper. Each record retains its original complete CAS SHA; only optional top-level pretty is removed. `provenance.json` pins the transformed fixture, source files and existing nine-role constructor fixture. Source: Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; accepted producer index `74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`. Upstream is Apache 2.0 (LICENSE), copyright Microsoft Corporation 2013–2014, author Leonardo de Moura.

Raw ABI is two borrowed object parameters (callback, Expr), owned object result. The original boxed wrapper owns both and decrements Expr then predicate after the call. No initialized dependencies exist in these rows.

The reached native `replace_fn` uses identity-only owning-result cache with **is_shared / !exclusive**, including MT rc1 and leaf Expr kinds. The different offset-aware C++ replace_rec_fn uses likely-unshared and `(identity, offset)` keys; its helper jobs are not semantically interchangeable with this arbitrary callback native. This fixture alone is source evidence. The runtime unit and 18-test retained-JVM results are documented in the research contract; native-receipt.json pins the parent-run five-line Lean --run oracle (no AOT/effectful-trace claim).
