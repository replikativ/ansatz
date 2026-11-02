# Maintained native Lean producer sources

This directory owns the native helpers used by the optional
[Lean JVM SDK](../../modules/lean-jvm/README.md) for trusted source compilation.
The exact supported toolchain is official Lean **4.33.1**, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, on
`x86_64-unknown-linux-gnu` with 64-bit words. A compatible-looking Lean version
or a successful local rebuild does not establish a supported producer identity.

| Source | Role |
| --- | --- |
| [src/NativeGeneralEntryEvidence.lean](src/NativeGeneralEntryEvidence.lean) | v2 entry discovery: native types, callable lookup, representation/layout facts and reachable structural IR. |
| [src/NativeStartupEvidence.lean](src/NativeStartupEvidence.lean) | Source-header and imported initialization provenance. Native import can execute native initializers; this is not evidence that a JVM initializer ran. |
| [src/TypedSourceExport.lean](src/TypedSourceExport.lean) | Genuine frontend elaboration, `.olean` production and structural declaration export. Frontend diagnostics go to stderr; structural NDJSON goes to stdout. See the [diagnostics contract](src/TypedSourceExport.diagnostics.md). |
| [legacy/NativeEntryEvidence.lean](legacy/NativeEntryEvidence.lean) | Frozen v1 entry helper for the explicit Nat, String and IO Unit convenience profiles. |

These are maintained source locations, not an installed producer bundle. The SDK
invokes explicitly supplied native executables; it does not compile these files
at runtime or discover helpers in a repository checkout. Source compilation also
needs the pinned installed Lean sysroot, a writable compiler cache and Linux
`prlimit`. Native metaprograms and compile-time IO execute as trusted code.

Precompiled artifact loading uses the JVM SDK and its ordinary Maven dependencies.
It does not need this directory, a native helper bundle, a Lean installation,
Python or Clojure CLI. Native frontend evidence is not a Java kernel proof
certificate.

## Bundle and cohort boundaries

[modules/lean-jvm/producer](../../modules/lean-jvm/producer/README.md) owns the
bundle manifests, archive/release records and SDK packaging configuration. The
paths in a bundle descriptor are relative to the extracted bundle, not to this
source tree. Preserve those published layouts and identities when moving sources.

The [v1 descriptor](../../modules/lean-jvm/producer/producer-bundle.example.json)
records the published v1 source/binary pairs. The
[v2 descriptor](../../modules/lean-jvm/producer/producer-bundle-v2.example.json)
records the general-entry, diagnostics-aware candidate; its
[archive record](../../modules/lean-jvm/producer/candidate-v2.json) remains
unpublished. The three current `src/` files match that v2 descriptor's source
hashes; the legacy entry source matches the v1 descriptor. The v1 typed exporter
has a different immutable source identity; the current typed exporter must not
be substituted into a v1 bundle.

The SDK's independent admission authorities are
[entry.clj](../../modules/lean-jvm/src/ansatz/lean/jvm/entry.clj) for v1/v2 entry
pairs and [producer.clj](../../modules/lean-jvm/src/ansatz/lean/jvm/producer.clj)
for startup/typed-export pairs. These include the original v2 entry pair as
compatibility evidence alongside the later admitted v2 pair. Each source/binary
pair is immutable: a descriptor's self-reported hashes cannot admit new bytes,
and independently admitted source and binary hashes cannot be mixed arbitrarily.

Editing, compiling, relinking or stripping a helper may change its identity.
Changes require a separately reviewed cohort, bounded native acceptance and the
actual public source cold/cache/artifact acceptance gate before new pins are
admitted. Keep supported earlier cohorts and historical receipts intact. Source
relocation alone requires no recompilation, pin change or receipt rewrite.

## Code lookup catalogue

`build-code-catalogue.py` builds the compact typed-Name lookup index used by the
engine code-demand path. It authenticates the source CAS index against its
independent expected hash; SQLite is an acceleration aid, not the source of
authority. It copies no declaration bodies and uses only the Python standard
library. Run `python3 build-code-catalogue.py --help` for inputs and limits.
