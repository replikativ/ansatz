# Private native observation capture

These files were emitted by pinned Lean 4.33.1. `provenance.json` records exact
source and capture hashes. The producer sources live in `tools/lean-producer/src`
at the repository root; the exact small fixture and observation probe inputs are
retained in this directory's `sources/` folder. The fixture uses its original
module name and differs from the broader current producer test fixture.

The probe first inventories defining modules, captures their actual product
roles, then emits type/layout observations and rechecks the products. The module
hashes are real captured `.olean` hashes. This is test input for the private
normalizer, not a registered producer cohort, source-build issuer, callable ABI
proof or public datatype admission. Missing closed builtin and runtime witnesses
must continue to fail explicitly.

This capture was regenerated with the producer sources identified by the current
provenance file; all three captured JSON files were byte-identical. Reproduce
with those exact hashed inputs. If producer sources change, regenerate and
compare the observations before updating provenance. Development-branch history
alone is insufficient provenance after a squash. Do not update JSON or hashes
merely to make a changed producer appear equal.
