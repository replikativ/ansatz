# Keep the kernel side lazy too

The accepted artifact contains 6,418,857 normalized expression DAG records. A
Java Expr[] or recursively hydrated ConstantInfo for all 65,994 declarations is
not an acceptable startup representation. This artifact is the trusted imported
basis; it does not authorize replaying all proofs during ordinary loading.

Use the existing format2 storage route as an offline preparation operation.
`ansatz.export.storage/import-ndjson-streaming!` already persists CI shells with
expression IDs while expressions remain in the file-backed ExprStore. Its raw
`ExprStore.readRaw(id)` path transfers records without deserializing Expr graphs.
Validate exact counts against the pinned audit (65,994 CIs, 342,605 Names, 590
levels including zero, 6,418,857 expressions), quotient state and all four PSS
roots before publishing a new manifest. Do not reuse Prelude's 2,314-domain
store-only wrapper or relabel a medium Init subset as full Init. The existing
ordinary Init/Mathlib loading paths and their performance remain unchanged.

For ordinary opening, restore env/expr/name/level PSS roots and an indexed typed
CI domain. `branch-loader` in storage.clj already shares lazy branch caches and
raw evidence sources. It resolves one CI shell when that name is requested.
`resolve-ci-shell :full` resolves that CI's proof body recursively, so invoking
it for every CI would defeat laziness. `:defs-only` is an existing proving-session
view, not full checking-shape evidence: never substitute its missing theorem or
opaque values for the complete source payload or weaken the admitted base API.
Keep raw shell/body IDs as the full evidence and materialize a genuine full CI
only when the selected runtime/checking operation actually needs it.

The current matched-base factory and exhaustive Java checking-shape readback
were designed/tested for Prelude. If they enumerate and hydrate every imported
CI, a new explicit lazy-base admission route is required, rather than merely
raising a count limit. It should validate the complete typed Name/kind/source
occurrence/winner domain and exact audited raw shell/checking-shape IDs up front,
bind the store roots plus native source arena to an opaque capability, and check
actual Java CI identity/payload on first materialization. Historical local
versions, full raw evidence and all existing mutation/replacement guards remain
required. No eager Java Expr graph is needed to compare immutable raw record IDs
whose source correspondence was already established by the offline audit.

The native guest graph and kernel Expr graph have different identity semantics.
The structural exporter may coalesce structurally identical Expr objects, while
native source nodes retain distinct source-index pointer identities. Do not make
the kernel-store Expr wrapper the universal canonical guest-node view. Keep the
native arena's source identity, and use the matched correspondence strictly for
logical/kernel projection. If an efficient Expr-level bridge needs a native-node
to exporter-ID index, produce that mapping from actual typed source Expr roots
under the same paired producer receipt; do not infer it from structural hashes.

The minimal benchmark should open a precreated full Init store, enumerate typed
CI metadata only, and fetch a small fixed set of required declarations. Record
wall time, heap, resolved CI count and hydrated Expr count. Then test genuine
original finalizer access on the lazy arena separately. Fast opening is not a
claim that every possible original import-extension callback remains cheap, nor
that full Init finalization/initializers have already been accepted.
