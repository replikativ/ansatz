# Native Init attribution selection and preflight

Native reset finishing previously scanned const/extra names from every public,
server and private ModuleData part, then rejected a name attributed to two native
modules. This differs from pinned Lean 4.33.1: `mainModule?` selects private data,
`irData?` selects the effective IR data, and `finalizeImport` inserts private
`constNames` followed by IR `extraConstNames` into `const2ModIdx` with
`insertIfNew` (first module wins). See
[Environment.lean at 819816](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Environment.lean#L2308-L2347).
Native reset now reuses the existing graph private/IR selector, checks actual
module-index getter results against the same finishing graph plan, and preserves
legal native aliases. Source-local attribution conflict rejection is unchanged.
The selected-array layout and full name-occurrence budget are checked before
header inspection, Name encoding or native queries and repeated on the actual
finishing World; earlier successful preflight is not authority. The graph
planner and preflight share one count expression, including module/request
occurrences; duplicates still count before deduplication. No limit defaults,
initializer policy, Source ownership or checked-union validation are widened.

For the authenticated 631-module descriptor whose SHA256 starts `62b168762b4e`,
the old all-parts scan counted 244,553 occurrences. The correct selection contains
66,124 private constant names plus 37,455 IR extra names: 103,579 raw occurrences
and 95,088 unique names for getter checks. The shared graph inventory adds 1,264
request/module occurrences, yielding 104,843 under the existing explicit 200,000
bound; a larger bound is unnecessary. These are bounded static descriptor/name
inventory observations, not measured guest fuel or an end-to-end reset result.
The earlier warm campaign reached native IO completion and then failed finishing
after roughly 2,050 seconds. The focused tests below establish the corrected
selection, early rejection, first-wins/getter verification and owner-preserving
failure behavior on small real Worlds/Sources with explicit transport/provenance
models; they do not establish a successful full P2 campaign. The portable record
is [native-init-attribution-preflight.json](../measurements/native-init-attribution-preflight.json).
