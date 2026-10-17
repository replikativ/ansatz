# Hosted checkpoints after guest import

This is an implementation plan, not an available restore API. The first target
is a completed guest `finalizeTransport` result immediately **before** Java
kernel projection/association. Restoring that result would skip repeating the
large guest import and extension-registration execution while retaining strict
kernel verification on restart. It must not silently turn a serialized Java
Environment into checked authority.

The existing [bootstrap archive](../src/prototype/bootstrap_archive.clj) remains
unchanged. Its `ansatz-frontend-bootstrap-archive/1` format deliberately rejects
native sources, kernel associations, executable identity capabilities, source
publications and opaque resources. A hosted checkpoint needs a separate format,
strict schema/version, and explicit expected manifest SHA256 at restore.

## Existing mechanisms to reuse

| Mechanism | Actual API/contract |
| --- | --- |
| Bootstrap streaming | `bootstrap-archive/write! path world header` and `restore path {:expected-sha256 ... :expected-lean-commit ...}` stream function/heap/global/state rows, preserve function metadata, and reject malformed/truncated/duplicate data. Reuse the bounded streaming mechanics, not the old format's admission rules. |
| Verified ModuleData | `module-store/open-verified world descriptor-path expected-descriptor-sha256 {:source-path ... :cache-size ...}` rehashes the source and index, verifies the descriptor, pins a private index inode, and exposes bounded lazy reads. It does not reparse every object. |
| Native heap | `NativeSource/contains-id?` checks reserved range membership without decoding. `lookup-node` returns immutable RC0 objects; `native-heap/lookup` resolves sources in order. |
| Strict kernel import | `imported-kernel/verify-constants world guest-values policy` projects/checks actual final constants. `associate-checked` verifies the actual guest root/map/quotient state against that certificate and installs protected ownership anchors. |
| Frontend recovery | Raw failures retain latest checkpoint/session and nested host-boundary alternatives. Frontend errors separately preserve the original owned compilation IO result under `:frontend-result`. These are diagnostic snapshots, not automatic retry permission. |

Related code: [module store](../src/prototype/module_store.clj),
[native heap](../src/prototype/native_heap.cljc),
[import verification](../src/prototype/imported_kernel.clj),
[finalization boundary](../src/prototype/module_import.clj),
[raw execution](../src/prototype/raw_interop.clj),
[frontend](../src/prototype/frontend.clj).

## First milestone: completed guest finalizer, strict host verification again

1. Capture the immutable raw invocation result after the actual guest finalizer
   returns `:done`, before `module-import/finish-finalization` consumes its owned
   IO wrapper or starts Java checking. Capture its matching returned raw session.
   Saving this boundary is not replacing finalization with a native Environment.
2. Stream the existing function table, overlay heap, globals and semantic world
   state. Preserve exact IDs, reference counts, function metadata, module guards,
   task/stdio state, heartbeat accounting and supported initialized global values.
   Do not enumerate or copy the underlying native object's complete graph.
3. Store explicit application roots with their ownership contracts: the owned
   finalizer IO result, owned Options and any deliberately retained Environment
   or import inputs. A stale `:result` register alone is not a root inventory;
   some completed control slots intentionally contain dead references.
4. Store verified native-resource descriptors and executable authority recipes
   as data, not open channels, callbacks, Java objects or duplicate function maps.
   This initial profile excludes source publications and Java kernel associations.
   Reject unrelated opaque resources and unsupported pending execution.
5. Restore resources and the streamed world privately, validate everything, then
   atomically publish a matching session/world/owned-root result. Bind host
   capabilities explicitly through the prepared runtime factory. No guest code
   runs while partially restored state is visible.
6. Resume through `finish-finalization` on the restored actual IO result. Repeat
   the host's strict Java projection/checking and exact guest-map association.
   This still costs kernel checking; it avoids the preceding guest registration
   execution. No restart speed or full Init compatibility result is assumed here.

A producer can retain this immutable finalizer snapshot while a later fork
consumes/checks its result. It must not create a second heap merely to archive
it. As with the bootstrap writer, verification should compare bounded individual
rows against the original snapshot rather than load a second complete world.

## Verified resource identity and guest IDs

A `module-store/Store` exposes `:base`, `:size`, `:digest`, and `:manifest` in
addition to its live backing resources. Its native IDs occupy the half-open
range `[base, base + size)`. Every decoded reference is reconstructed using that
base; changing the base without relocating **all** world references corrupts the
snapshot.

`open-verified` currently chooses `base = world.next-id`, then advances `:next-id`,
`:stats/:allocations`, and `:heartbeat-allocation-offset`. Therefore calling it
naively on an already restored world is wrong: both IDs and counters change.
The checkpoint loader needs an explicit saved-base source reopening adapter
(or an isolated reservation world followed by validated source-only attachment).
It must preserve the saved world's counters exactly and validate:

- Every saved native range has the exact saved base/size and no overlap with
  another native range or the overlay heap; no source can shadow another object.
- `:next-id` exceeds every allocated overlay ID and every reserved native range.
- Every live guest reference resolves to the overlay or an attested native range.
  Range checks need not decode eleven million immutable objects.
- Descriptor SHA, source SHA/size, index SHA/size, manifest/profile and module-part
  metadata match the exact checkpoint manifest, not merely similar file names.
- The reopened resource satisfies the existing verified-store contract; arbitrary
  `NativeSource` implementations do not inherit its projection-reuse authority.

The writer must receive portable descriptor/source mappings from the caller and
match them against the actual Store's identity fields. A Store does not retain a
portable descriptor path, and an open FileChannel is not a reproducible resource
recipe. Paths are caller-supplied locations for pinned bytes, not authority.
Closing a Store invalidates every restored fork using it; expose explicit shared
resource lifetime rather than closing it after loader return.

## Executable and capability identity

EDN equality does not preserve `identical?`. The runtime intentionally uses
identity for trusted/admitted executables, units, initialized entries and checked
constants. Serialize references to canonical tables, then reconstruct aliases:

- Deserialize each function exactly once into `world.functions`, including all
  metadata. Record executable authorization as function names plus exact code /
  provenance evidence. Reattach every authorized function by lookup in this
  canonical map, never independently deserialize another equal function map.
- For the first full-import profile, allow only imported catalogue authority:
  imported declaration identities, exact pinned catalogue/alias/ABI artifact
  hashes, and the authorized executable-name set. No new source-unit receipts,
  initializer completion claims or kernel associations are manufactured.
- Validate selected declaration rows and exact executable metadata against the
  authenticated checkpoint/captured catalogue. Generated global-wrapper targets
  also belong to the canonical function table; they are not independent source
  declarations.
- Recreate bindings through explicit host factories and verify required extern
  signatures/capability profiles. Do not serialize handler closures, code caches,
  mutable native channels or an arbitrary raw session's JVM internals.
- Require the pinned Lean commit, runtime schema and actual runtime/kernel build
  identity. A matching Lean commit alone is insufficient: cache layouts and
  primitive semantics can change during development. Default to exact restore;
  a program/runtime upgrade requires a separate explicit validated migration.

The format needs whitelisted constructors for `RawNativeScalar` with validated
unsigned payloads and exact IEEE Float/Float32 bit encodings. Existing scalar
byte-preserving helpers provide the semantic contract. Generic EDN NaN or Java
object serialization would lose bits or introduce unsupported object authority.

## Later milestone: checked Java Environment reattachment

Start with strict host rechecking after restart. Only add a faster checked-kernel
cache once that path is correct and measured. Existing
[Ansatz kernel codecs](../../../src/ansatz/export/codec.clj) and
[replay](../../../src/ansatz/export/replay.clj) are useful building blocks, but
ordinary deserialization or `replay-one` with verification disabled is not by
itself evidence that an artifact was checked under the required policy.

A checked cache must bind the actual guest final constant map, exact guest IDs,
quotient/header state, checked declaration set, assumptions/unsafe/compiler-marker
policy, kernel implementation identity, and the completed-world checkpoint hash.
An explicitly pinned artifact from an authenticated successful checker run can
be a new trust boundary; a serialized boolean claiming “verified” cannot.

Reconstruct canonical Java ConstantInfo objects once, rebuild immutable Env views
from those same objects, and reattach only guest roots/maps validated against
them. Saved source-import receipts later need these *same* Java CI/Env identities,
not separately decoded equal copies. Existing codecs should be assessed for DAG
sharing and deep proof terms before choosing a persistence layout.

Ownership must not be counted twice. A snapshot saved after association already
contains the RC owners belonging to protected anchors. Reinstalling those aliases
must not call `associate-checked` as though the anchors were absent and retain
again. The initial pre-association milestone avoids this complication. Future
source publication support additionally needs canonical unit receipts, registered
module-data owners, logical region anchors, and actual initialized-entry identity.
Keep that outside the first format profile.

## Initial verification scope

Use tiny worlds and verified small ModuleData resources first: round trip at a
nonzero native base, overlay-to-native edges, closed/modified backing resources,
range collisions, tampered digests/code/ABI/metadata, owned result consumption,
authority identity reconstruction, and independent restored forks. Compare strict
post-restore checking with the original small finalizer certificate. Reject partial
saves, live frames, unsupported external resources and incompatible runtime builds.
Only then archive a completed full Init boundary once; do not repeat the large
guest import or run full-world copy benchmarks merely to test the format.
