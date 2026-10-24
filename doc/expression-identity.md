# Expression identity across stores

`Expr.isEqp` is actual Java object identity. This matches Lean's pointer check
(`src/kernel/expr.h`, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, line 112).
Equal expressions reconstructed as separate objects continue through structural
equality and definitional equality, including the existing memoized kernel
expression maps and pair sets.

The former shortcut treated equal nonnegative `storeId` integers as pointer
equality. Those integers are local addresses: independent expression stores,
resolvers and branch revisions can assign zero to different expressions. Two
actual `ExprStore` objects containing `Sort 0` and `Sort 1` at address zero
therefore compared equal through that shortcut. The kernel could then accept
`result : Sort 1 := a` with an axiom `a : Sort 0` imported from the other store.
The pointer check now rejects that alias and normal type checking rejects the
definition.

`storeId` retains its existing integer field and address format for diagnostics.
Neither readers assigning it nor `shareCommon` propagating it grants equality.
The binding trace calls a coincident address `same_local_expr_id`, rather than
claiming that it establishes a common store. No store format or Expr field layout
changes are required.

A cache hit still returns the same actual object. After cache eviction a reader
may reconstruct an equal, distinct node; structural caches and definitional
equality continue to recognize it. The performance cost of losing the integer
shortcut requires measurement in representative checking runs. A future
optimization must establish complete source and snapshot identity before
granting any stronger shortcut.

This correction applies to newly loaded corrected Java classes. A running JVM
retains its already loaded classes and needs a fresh process for the correction.
Existing imported or custom-admitted declarations are not retroactively checked
by changing the equality predicate.

The [focused regression record](expression-identity-validation.json) passed
125 tests / 580 assertions with fresh compiled classes and a 384 MiB heap. It
covers actual independent stores, valid equal declarations, binder domains,
structural hash collisions, cache eviction, sharing, and independently captured
Clojure resolver revisions. All 326 input hashes matched after process disposal.
Full fresh Init checking and representative performance remain separate gates.
