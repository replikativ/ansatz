# Original UInt16 rows

Four original accepted rows provide UInt16.decEq and UInt16.toNat, raw and boxed.
Their bytes/typed Names were authenticated in the sixteen-row layout/scalar
inventory and verified against the original CAS and accepted index-derived SQLite.
`provenance.json` pins this exact subset, Lean commit, source hashes and license.

Raw equality is owned[uint16,uint16]→uint8. Raw toNat is owned[uint16]→tagged.
Both genuine boxed wrappers use owned tagged arguments and tagged results; UInt16
boxes are immediate Long values, not UInt64-style eight-byte heap boxes. Native
semantics come from lean.h:2054 and2075. No arithmetic family is implemented here.

The engine admits canonical 0…65535 raw scalar inputs, literals and unbox values.
It rejects negative/wide values instead of claiming parity for malformed raw IR:
pinned ir_interpreter.cpp loads small-width literals without narrowing. The model
checks therefore distinguish canonical source behavior from explicit profile
rejections. Packed scalar storage is exactly two little-endian bytes.

The original rows are authentic; the transport/storage/callback callers in
u16-checks.clj are labeled research models. No native oracle or interpreter JVM
was executed by the author. Runtime observations are supplied separately by the
parent's retained test process.
