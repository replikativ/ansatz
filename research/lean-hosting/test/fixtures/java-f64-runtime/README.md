# Original Float family and matching native oracle

The 18 original CAS declarations are the nine roots Float.ofBits/ofModel,
UInt64.toFloat, Float.sub/mul/div/beq/decLt/toString and their genuine boxed
wrappers. Only optional top-level pretty text was removed. `provenance.json`
pins each original record separately from the derived fixture bytes. ofBits and
ofModel retain distinct original Names despite sharing one native symbol.

`native-oracle.py` runs the small `Oracle.lean` with an installed matching
Lean 4.33.1 binary, feeding 278 fixed runtime word/Nat vectors. `Profile.cpp`
is a small read-only query shim for the same process's rounding mode and numeric
locale and verifies the actual linked runtime's raw ofBits quiet-NaN word;
it provides no replacement Float implementation. Its boxed UInt8 exports serve Lean
`--run`'s native opaque lookup, acquire no heap owners and never change fenv or
locale. The script caps g++ address space at 256 MiB, writes its shared library
under the repository's ignored target directory, and records compile exit,
flags, source/library hashes, and native exit. The native receipt identifies
FE_TONEAREST, LC_NUMERIC=C and raw quiet-NaN word 0x7ff8000000000000. It pins the matching native binary/runtime/libc,
not the executable that originally produced the accepted checkpoint.

The oracle covers codecs and special values; finite arithmetic and canonical
NaN results; exact decimal ties and adjacent values; unsigned conversion; and
native Float.ofNat for arbitrary-Nat literal rounding and overflow neighbors.
Native Float.toBits intentionally canonicalizes NaNs, so these arithmetic
vectors do not assert native/JVM raw NaN payload parity. Unsafe signaling words
are tested separately in the Java engine's internal transport, without decoding.
Public Double views/replies have Java's signaling-NaN representation limit.

Reproduce with `python3 native-oracle.py`; `LEAN_BINARY` can specify another path
to the exact matching native toolchain. No JVM, Init IR image, or Mathlib load is
part of this oracle. The Java suite consumes the pinned results, not a system
Python implementation of floating-point or formatting.

Original Lean source copyright Microsoft Corporation and contributors,
[Apache 2.0 license](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
See pinned [lean.h](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/include/lean/lean.h),
[object.cpp](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp),
and [OfScientific.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/Data/OfScientific.lean).
