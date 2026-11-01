# Original Level equality runtime evidence

Pinned Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (4.33.1).
Accepted index: `74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`.

The two original rows are `Lean.Level.beq` (borrowed tobject/tobject → uint8)
and its genuine owned boxed wrapper. Only top-level pretty is removed; per-row
SHA256 identifies complete original raw CAS bytes. The wrapper invokes the raw
borrowed extern, releases both owned arguments, then boxes the result. Rows and
upstream source hashes are pinned in provenance.json. Upstream code is Apache-2.0;
see LICENSE and source headers.

Pinned `Lean/Level.lean:255–256` declares `lean_level_eq`.
`kernel/level.cpp:127–158` compares kind, low32 cached hash, pointer identity,
then Name for param/mvar, or cached depth and ordered children for succ/max/imax.
It does not normalize max/imax or implement `lean_level_eqv` equivalence.
`Lean/Level.lean` declares only `lean_level_mk_data` and `lean_level_eq` externs;
together with the existing data primitive this completes that source-file family.

Constructors and dependencies are reused from the independently pinned sibling
Expr equality fixture; no assets are copied or regenerated. That fixture's
existing native oracle exercises Level comparisons through Expr.sort/const.
It supports the shared structural relation, not a newly executed direct
lean_level_eq oracle. No new native process was run for this fixture.

The focused Java suite separately labels graph/cache/cycle/budget adversaries as
models. It checks genuine constructor/owned-wrapper paths, borrowed-entry fences,
owned AP/import, all six Level kinds, order/hash/depth/flag rules, deep/shared DAGs,
cycles, bounded work and interruption. Runtime results are reported by the root
campaign after building a new immutable artifact.

`python3 verify.py` checks fixture/shared-evidence hashes and exact ABI. Optional
`--lean-repository PATH` verifies pinned source blobs with git show, and
`--store PATH` verifies the original complete CAS byte hashes. Neither mode
invokes Lean/native compilation or changes fixtures.
