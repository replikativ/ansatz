# Pinned frontend bootstrap bundle

Release plan, 2026-10-29. No frontend bundle has been published by this work.
The first Java frontend release can distribute IR derived from pinned upstream
Lean and its matching prepared state. Runtime users should not need a native Lean
build merely to load a supported Lean file. This packaging does not establish
parser/elaborator acceptance; the Java runtime still needs the campaign gates in
[the lazy-code plan](JAVA_LAZY_CODE.md).

## Publication

Reuse [ansatz-stores](https://github.com/replikativ/ansatz-stores), which already
publishes immutable, SHA-pinned multipart store releases with deterministic
archives. Keep the frontend manifest, root specification and rebuild tools in Git;
put the bulk generated payload in versioned release assets. Reuse download cache,
integrity checks, offline/mirror configuration and interrupted-download handling
where their actual contracts fit.

Give frontend bundles their own artifact kind, schema, runtime ABI and release
names. They contain executable guest code and initialized frontend state; they
must not masquerade as a kernel declaration store or inherit its checking claims.
Preserve the existing Mathlib store and index contract. Whether frontend entries
share an index file or use a separate one is an implementation decision after
the first complete bundle is measured.

## Contents and identity

The manifest must bind:

- Lean version and exact source commit, exporter/build revisions and invocation,
  target word width, runtime ABI, codec and supported entrypoints.
- Original typed Name-to-declaration identities, exact ABI/borrow/type metadata,
  initialized-value roles and authentic module initialization plans.
- Prepared global/ref/closure graph roots and their initialization coverage.
  Closure descriptors need authentic headers; unused bodies remain demand-loaded.
- Required imported frontend module/extension data and matching lazy kernel-store
  roots. Kernel stores alone do not reconstruct parser registrations.
- Per-part hashes, sizes, provenance and upstream attribution. A supplied hash
  string is not source authority; acceptance binds a trusted manifest/source.

Use an indexed pack or equivalent bounded resolver so the JVM can look up one
header/body without eagerly parsing the entire Name index. Strip display-only
pretty text from the execution representation, while preserving an auditable
mapping to authenticated original rows. A transformed packed body needs its own
hash and extraction/codec identity; its hash is not the original row hash.

## Measured size and reduction work

The existing producer catalogue has 375,258 distinct declaration blobs totaling
1,389,150,335 content bytes, plus a 120,853,740-byte index: **1,510,004,075 bytes**
(about 1.406 GiB) raw. This is the complete existing catalogue, not a measured
minimal frontend bundle. All indexed blob paths were present in the audit;
the size inventory did not rehash every blob body.

Legacy bootstrap archives, the 610 MB checkpoint and roughly 2.36 GB of module-data
transport overlap with this code/state content. Adding them all together is not
an intrinsic frontend requirement. Neither the final accepted Java bundle size
nor its compressed size is established yet.

Before publishing, measure an actual accepted profile with packed Names, no
pretty-text duplication, bounded indices, compression and separated module/state
parts. Distinguish download bytes, installed bytes, JVM retained heap, cumulative
allocation, cold startup and warm file-loading latency. Demand loading improves
resident preparation cost; it does not by itself remove shipped bytes. A smaller
entrypoint slice cannot omit dynamic callbacks or module-init state merely
because static calls do not mention them.

## Self-hosting

Executing the original Lean frontend/compiler on the Java engine is the campaign
goal. Rebuilding that frontend from Lean source is a subsequent bootstrap gate.
Even a self-hosted release needs a runnable seed, supplied libraries and module
metadata; it does not eliminate distribution requirements automatically.

A later release may reduce the seed and regenerate the rest, if reproducibility
and measured build/iteration costs justify it. The first release can ship a
reproducible prepared bundle and use that same engine for normal REPL/file work,
without forcing every user to rebuild the compiler at startup.
