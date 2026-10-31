# Original FoldConsts pointer-hash cohort

`original-rows.json` preserves fifteen canonical source-cohort witnesses, including
three hash bodies, bucket equality, closed empty-seed roles and high-level
foldUnsafe entries. `execution-rows.json` is the finite original FAP/PAP closure
of both foldUnsafe variants plus `Lean.Expr.getUsedConstants`: 54 rows / 160,023
raw CAS bytes, zero initialized dependencies. Arbitrary dynamic callbacks are
outside this static closure. Only optional top-level `pretty` was removed.

Each row was independently reread from CAS, SHA-256 checked and matched by exact
typed Name against accepted index `74d833d5…`. Provenance pins complete identities,
normalization, bounds and eight source files at Lean `819816b2`. These ordinary
Headers are metadata; authentic source bytes and the high-level input protocol
are trusted-loader obligations. Apache 2.0 upstream terms are in `LICENSE`.

The runtime's explicit policy binds contains/insert/rehash in that order. Only
these original bodies gain certified target-identity hashing. Admission requires
the original high-level route with its empty target-built seed; a foreign
populated/prebucketed native map is unsupported and is not universally detected
from untyped Node shape. Imported Expr keys may be inserted into a fresh map.
No original IR body is rewritten and no existing capsule is rehashed.

`FoldConstsOracle.lean` is a bounded parent-executed pinned official `--run`
semantic oracle. `native.stdout` is its observed fifteen-line output: source
getUsedConstants twice and direct foldUnsafe callback agree for sharing/equal
construction requests, all traversal forms, level exclusion and a repeated DAG.
No numeric hash/address or physical allocation-identity comparison follows.
Native execution belongs to the parent; the author ran no native/JVM test runner.
See [runtime scope and validation](../../../research/JAVA_POINTER_HASH_RUNTIME.md).
