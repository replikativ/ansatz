# Original Lean UInt8, UInt32 and USize declarations

The 46 declarations in `original-rows.json` are the 23 UInt8/UInt32/USize roots
in the original header extern inventory and their 23 genuine boxed wrappers,
exported from Lean 4.33.1 at commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

The roots cover thirteen USize operations, six UInt32 operations and four UInt8
operations: arithmetic, comparisons, bitwise shifts/and, Nat conversions,
UInt32-to-UInt8 conversion and USize representation. Existing engine operations
are included for exact ABI continuity. The selection is finite inventory
coverage; it does not assert all rows execute or are supported. No UInt64,
Float, signed Int or absent arithmetic primitive was added speculatively.

Only optional top-level `pretty` was removed. Bodies, ABIs and other metadata are
unchanged. Each record pins its original CAS blob; `provenance.edn` separately
pins the derived fixture. USize uses the campaign's 64-bit unsigned profile;
Java signed long storage must preserve that unsigned meaning.

Upstream: `src/Init/Prelude.lean`, `src/Init/Data/UInt/Basic.lean`,
`src/include/lean/lean.h`, `src/runtime/object.cpp`, `src/runtime/mpz.cpp` in
[the pinned repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors; derived material is under
[Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
