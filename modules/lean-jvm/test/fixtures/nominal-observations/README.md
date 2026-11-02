# Private native observation capture

These files were emitted by pinned Lean 4.33.1 using the producer/test source
snapshots committed with this capture. `provenance.json` records exact source and
capture hashes. Later producer development may change those source files; use
the historical snapshots identified by these hashes when reproducing the probe.

The probe first inventories defining modules, captures their actual product
roles, then emits type/layout observations and rechecks the products. The module
hashes are real captured `.olean` hashes. This is test input for the private
normalizer, not a registered producer cohort, source-build issuer, callable ABI
proof or public datatype admission. Missing closed builtin and runtime witnesses
must continue to fail explicitly.
