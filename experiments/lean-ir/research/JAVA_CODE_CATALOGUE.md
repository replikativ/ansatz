# Compact authenticated base-code catalogue

Implemented research infrastructure, 2026-10-30. This is a host-scoped source
resolver for original exported Lean declarations. It runs no guest code and is
not an engine heap value or a whole frontend acceptance gate.

## Format and producer

Each sorted 64-byte record contains SHA-256 of an exact typed Name encoding,
followed by the 32-byte original declaration blob digest. Sort both fields as
unsigned bytes. Equal Name digests form a contiguous collision range; the reader
checks the actual typed Name in each authenticated candidate before selecting it.

`lean-typed-name-prefix/1` starts with anonymous byte zero, then walks prefix to
leaf: kind byte one for String or two for Num, big-endian UInt32 UTF-8 length,
then exact UTF-8 leaf bytes. Numeric leaves are canonical decimal strings, as in
the pinned exporter. Malformed names, invalid Unicode, more than 256 segments or
more than 1 MiB of encoded Name reject. Tags and Unicode spelling remain distinct;
neither Clojure hashes nor Unicode normalization define source identity.

`scripts/build-java-code-catalogue.py` takes an accepted original index pin,
read-only source store and its derived Name database. It streams/hash-verifies the
original index and cross-checks **every exact Name/digest plus cardinality** against
the database before publishing an output manifest. SQLite BLOB ordering produces
the fixed records without retaining the full catalogue in process memory.

The manifest binds schema/codec, original index digest, data digest, record count,
record size and sort convention. Its bytes are deterministic and contain no
machine-specific paths. Generated bulk data stays outside Git.

## Reader and resource scope

`research/java-ir-baseline/catalogue.clj` provides
`ansatz.research.ir.catalogue/open`, `lookup`, `source-token`, `descriptor` and
`close!`. It uses ordinary JDK positional FileChannel reads and existing JSON
support; there is no SQLite/JNI/Python runtime dependency for lookup.

Open requires independently accepted manifest and original-index pins. It checks
data size, full digest and unsigned ordering through the same retained channel.
The accepted profile allows at most 500,000 records. Lookup binary-searches the
Name digest, checks bounded original CAS bytes against the selected digest and
compares the exact Name. Default blob limit is 8 MiB, configurable up to 64 MiB.
Missing Names return nil. Stat guards check ordinary file replacement/rewrites
before and after both successful and missing lookups.

Lookups and close serialize per resource; close is idempotent and later lookups
reject. Publish immutable files. The stat guard is not a defense against a host
that deliberately rewrites content and restores metadata. The source token
contains only scalar pins/counts, not a channel, Name map or mutable guest state.
Host/session code owns the reader lifetime; it is never embedded in an engine
fork. Close a live reader before reloading its deftype namespace in a REPL.

This resolver covers the pinned **base CAS**. Per-request runtime-file overlays
and dynamically authorized compiler output need their own explicit accepted
resolution policy. Do not globally merge unrelated `main` definitions or infer
module initialization/kernel authorization from successful source lookup.

## Evidence

The real catalogue has **375,258 records / 24,016,512 bytes**, replacing the
120,853,740-byte JSON Name index. Original declaration blobs are unchanged and
still total roughly 1.389 GB raw. This is an index reduction, not a claim that the
complete frontend bundle is 24 MB or that its compressed size has been measured.

The retained 384 MiB REPL opened that complete index and resolved all twelve
original ref declarations/wrappers plus a private hygienic Name containing numeric
segments to their exact original digests. Six bounded JVM tests / 40 assertions
cover codec parity, authenticated collision scans, all pin failures, bounds,
missing Names, resource closure, lightweight tokens and file replacement during
both hit/miss lookup. Two Python producer tests pass. CI uses only tiny temporary
companions, not the full campaign store.

The combined isolated runtime/catalogue gate passes 392 test executions / 13,790
assertions at 384 MiB. This adds the source-lookup seam needed by demand-code
drivers without restoring the legacy frontend or parsing the whole JSON index.
