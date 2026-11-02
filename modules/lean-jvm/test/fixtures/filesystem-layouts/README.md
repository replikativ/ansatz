# Independent native layout evidence

`Main.lean` is an Ansatz-owned fixture defining ordinary constructor and
projection wrappers, not replacements for original Lean runtime factories.
The existing pinned TypedSourceExport producer compiled it under Lean 4.33.1,
commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Linux x86-64.
`provenance.json` records the exact source/capture hashes, producer source/binary
identities and resulting compiled product identity.

The SDK resource `META-INF/ansatz-lean-jvm/filesystem-layouts.jsonl` is that
actual 70-declaration stream, including original boxed
wrappers. It observes Metadata/SystemTime construction and projections, all 19
IO.Error constructors, Option, EST.Out and FileType values. Scalar writes prove
that Metadata stores size, links and type at offsets 0, 8 and 16 respectively;
source field order alone is not authority for this allocation.

The stream is stored once under `resources/`; the tests consume the packaged
copy rather than a duplicate fixture. FilesystemLayouts
requires the exact bounded bytes and SHA-256 before issuing its immutable layout
authority. Current original primitive Headers still require independent source,
Name, role and ABI checks. These fixture Headers must not be relabelled as
canonical runtime declarations.

`test/filesystem_layout_checks.clj` executes the original constructor/projection
IR through both interpreter drivers. `test-java/FilesystemLayoutChecks.java`
checks host-side factories and pre-allocation domain refusal. Neither test
claims arbitrary custom datatype interop or general public IO.Error decoding.
