# Explicit checkpoint producer and consumer identities

The archived checkpoint was produced under host implementation `50f...`.
The globals optimization changes the interpreter, so it is a different consumer
implementation. The old restorer's `:implementation-sha256` retains its original
meaning. This experiment introduces separate APIs while preserving the original
manifest, wire format, factory and restorer.

```mermaid
flowchart TD
  P["Pinned producer recipe + reference inventory"] --> F["Closed factory constructor"]
  C["Pinned consumer resource/class inventory"] --> F
  L["Fresh source-only loading attestation"] --> F
  F --> CAP["Issued factory capability: producer P, consumer C, profile"]
  M["Externally pinned original manifest + data"] --> R["New restore consumer"]
  CAP --> R
  R --> V["Parse, verify resources, reconstruct code, authorize bindings"]
  V --> U["Restored precheck world + owned resource lease"]
  U --> K["Separate fresh kernel checking"]
  K --> S["Resident source workflow"]
```

`prototype.globals-consumer-factory/make-factory` authenticates the exact original
recipe, original producer references and independently approved consumer
inventory. It returns an issued capability whose descriptor and reconstruction
callback live in a private weak registry. An arbitrary function, map, or plain
instance of its public zero-field class is not an issued factory.

`prototype.restore-consumer/restore!` accepts that capability, an external
manifest digest, the producer preparation, expected consumer identity, resource
resolver and explicit mutable backend/fuel. It retains the original bounded
parser, descriptor/data verification, resource-lease cleanup, canonical function
reconstruction, binding signatures and executable-authorization checks. It returns
`:status :restored-precheck` and `:strictly-checked? false`, with separate
`:producer-preparation`, `:consumer-implementation-sha256` and
`:compatibility-profile` fields. Restoration does not install a checked kernel
Environment or run guest initializers.

## Closed selected-resource profile

The original producer inventory has 242 rows. The current consumer selects 255:
the original entries except the two legacy factory/restorer sources, the approved
`mutable.clj` substitution, and fixed additions for the compatibility APIs,
existing optional consumers, Java provenance and selected runtime classes.
Its selected support directory contains exact copies of only
`bootstrap_archive.clj`, `checkpoint_wire.clj` and `declaration_store.clj`.
The adapted seed uses the new factory's constants, so the old factory/restorer
need not be available on its classpath.

The additional class rows include both `GlobalsOverlay` and its nested `Hint`,
all three existing `HeapOverlay` classes, and `TypedLongMemo`. Java source paths
and the exact five producer build scripts record filesystem provenance; they
are not classpath namespaces. Actual selected class resources are independently
hashed.
Clojure source/resource URLs must match the selected classpath. The inventory
means reviewed available project resources, not that every namespace executes.

A trusted fresh launcher must validate selection before loading namespaces,
reject project `__init.class` shadows, capture the original recipe/resolver bytes
under their external pins, and prohibit namespace reloads or Var replacement.
The public constructor cannot infer that history from current disk hashes. The
consumer digest is externally pinned so compatibility source files can be
included without a self-hash cycle. Driver/controllers have separate captured
source pins.

## Validation boundary

The focused suite exercises closed-profile rejection, parser/envelope shapes,
forged capability rejection and real canary Store failure cleanup. Read-only
private helper tests are isolated white-box checks, not a fabricated successful
archive reconstruction. The corrected focused suite passes 13 tests / 124 assertions.

The first genuine constructor probe stopped during pre-project loading because
five build scripts were incorrectly treated as classpath resources. It opened
no checkpoint, acquired no native lease and ran no guest code. The corrected
profile checks those exact script files as provenance, keeps namespace/class
resource checks strict, and receives a new consumer implementation identity.
The corrected genuine host-only constructor probe passed in 10.03 seconds with
442,605,568 bytes peak process-group RSS and no guard stop. It created an issued
factory capability after authenticating all 255 inputs; it did not invoke the
factory, open a native lease, restore a checkpoint or execute guest code.
The full archive run remains a separate execution gate.
The existing narrow checkpoint has a different producer contract and is not
silently accepted as a small positive fixture for this full `/2` profile.
The complete runtime regression suite now passes 848 tests / 89,380 assertions
with the selected support overrides. The actual externally authenticated
archive/seed/public-file workflow remains an independent execution gate.


This layer remains an optional experiment rather than a published `ansatz.lean`
API. Its three support overrides need the explicitly configured experimental
classpath; default Ansatz packaging does not provide that staging directory.
The [validation receipt](../measurements/restore-consumer-validation.json) records
runtime source pins, selected inventory and the focused/full test results.
