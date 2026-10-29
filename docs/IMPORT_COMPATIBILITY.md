# Export and interpreter compatibility

The NDJSON parser accepts declared lean4export format versions `3.0.0` and
`3.1.0`. A metadata header with a missing or unsupported format version fails
before later records are parsed or declaration callbacks run. Headerless record
fragments remain supported by the low-level parser for existing fixtures and
composition APIs; their acceptance does not establish a producer/toolchain pin.

Grouped inductive/constructor/recursor, mutual declaration, and quotient records
are implemented. Parsed declarations still require kernel admission: parsing is
not proof checking. A recognized format version does not promise compatibility
with every Lean release using that format.

The reproducible bundled generation profile in `ansatz.bundle` pins Lean
`4.33.1` and exporter format `3.1.0`, with producer identities and artifact hashes.
Its policy is stronger than the general parser's format check. Historical
`4.29.0-rc2` catalogue notes describe earlier cohorts, not the current bundle pin.

The parallel Lean interpreter campaign owns its runtime/frontend toolchain and
loader acceptance work. Changes to that pin should coordinate the frontend,
exporter, imported declarations, runtime IR/extern ABI, and companion metadata.
This stabilization does not upgrade that toolchain or regenerate Mathlib/CSLib.

Remaining issue #79 work is to inventory and refresh the desired library stores
against the chosen interpreter cohort, and to establish whether the historical
kernel trace patch still needs rebasing. Loading unchanged Lean sources and
bidirectional DSL/Lean composition remain acceptance gates in
`experiments/lean-ir/research/LEAN_HOSTING_CAMPAIGN.md`.

# Differential codec boundary

The Malli differential lane currently refuses declared bounded integer/string
schemas that require a `Subtype` value. The codec does not yet construct the
bound proof and `Subtype.mk`; a clear refusal precedes input generation and
execution. The same refusal applies to bounded scalars nested in supported
collections and records. `[:int {:min 0}]` retains the plain `Nat` carrier and is
accepted. This does not remove refinement types from ordinary definition typing.

Generator size limits for an unbounded declared schema are only sampling limits;
they do not change its kernel carrier. Proper refinement-value codecs remain
future work.
