# ModuleData transport experiment

The native boundary exports **v2 ModuleData**, before `finalizeImport` and
`loadExts`. It never exports a native finalized Environment, executable closures,
external handles, or native addresses. The guest must rebuild import state and
execute the original Lean extension callbacks using its own initialized runtime.

`native/build_module_data_transport.sh` builds the pinned 4.33.1 producer with
PIC. PIC avoids executable COPY relocations hiding initialized shared globals.
The GCC helper loads `libgcc_s` before Lean's shared library to keep its local
C++ rejection handlers compatible with the selected unwinder.

The full default Init import request consists of separate runtime and meta
imports, both `importAll=false`, `isExported=true`. The actual native
`importModulesCore` supplies canonical module order, effective flags, selected
public/server/private parts, and runtime/comptime IR parts. The portable file
preserves these choices. No initialization callbacks are transported.

The initial full Init artifact contains 11,233,359 objects across 631 modules.
It took 43 seconds to export with one native worker and peaked at 1.03 GB RSS.
Independent full graph/part validation plus verified-index publication took
2 minutes 45 seconds at 218 MB RSS. A fresh JVM with a 256 MB heap reopened the
verified full artifact in 13 seconds inside the API, with zero hydrated heap
objects. These are local experiment measurements, not general runtime guarantees.

## Immutable guest storage

`prototype.module-store/load-file` validates every JSONL node before returning a
world, including the pinned commit, bounded layouts, UTF8, scalar byte storage,
all edges in discovery order, complete reachability, inventories, source digest,
and the ModuleData/import/extension summaries. Proof bodies are validated as
objects and edges without constructing a permanent in-memory copy of them.

A 44-byte disk index per node stores offset, length, and SHA256 of its JSON row.
Imported IDs reserve a snapshot-local disjoint range; they are not native
addresses. The world retains a `:native-imports` vector of verified sources.
`prototype.native-heap` exposes range membership without reading any node and
immutable RC0 lookup. A bounded cache lives in the source, outside the guest
world; it stores no mutable guest state. Every uncached read verifies its row
hash, so modifying a backing file cannot silently replace the node in a fork.

Imported nodes remain RC0. Retain, release, and persistence operations recognize
verified ranges without recursively walking the whole imported graph. Updating
an imported object requires ordinary runtime copy-on-write; overriding its
reserved ID is rejected. Both reference and mutable machines read the same
immutable field vectors. Mutable runtime allocations retain their existing
mutable field arrays.

The source must outlive all snapshots using it. Explicitly closing it invalidates
lookups. Channels and derived caches are not EDN archive data. Durable archives can retain
the portable descriptor and reattach it with `module-store/open-verified`.
The caller must pin the descriptor SHA256 obtained from the complete validator;
reopening rehashes both the source and binary index before using their offsets,
without reparsing every proof object. The descriptor/index publish only after
all validation succeeds. `native/check_module_data_transport.py SOURCE --publish
DESCRIPTOR` creates this verified artifact. The source and index can move between
machines; pass the new source path explicitly when reopening.

## Representation boundaries

A raw immediate stores the unsigned **unboxed native payload**. It cannot be
interpreted as Nat or Int until its typed primitive is known: the native word
for small Int -1 is also a valid Nat 4294967295. MPZ nodes preserve signed semantic
values and identity. Strings preserve UTF8 bytes, codepoint length, identity,
and embedded NULs. Constructor scalar tails include native allocation padding;
strict kernel projection accepts that padding only with imported layout evidence.

`ModuleDataTransport.mkVirtualPart`, `mkRequestedImport`, `mkImportedModule`, and
`assembleImportState` reconstruct the exact pinned private ImportState layout
using guest arrays/maps. `finalizeTransport` invokes real guest `finalizeImport`
with extension loading enabled. Its virtual compacted regions are guest owners,
not native pointers: native freeing/read operations must never be invoked on
these virtual values.

The small native canary exercises shared object identity, strings with embedded
NUL/non-BMP text, signed/unsigned immediate ambiguity, large MPZ values, arbitrary
scalar bits, and a deliberately constructed NaN payload. Closures and external
handles fail explicitly rather than being stringified or silently omitted.
