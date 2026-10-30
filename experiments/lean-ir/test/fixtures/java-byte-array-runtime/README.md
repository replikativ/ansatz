# Original Lean ByteArray declarations

The eight declarations in `original-rows.json` are `ByteArray.mk`, `get`, `size`,
`push` and their four genuine boxed wrappers, exported from Lean 4.33.1 at
commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. These are the four ByteArray
extern roots in the original header inventory.

Only optional top-level `pretty` was removed; bodies, ABIs and other metadata are
unchanged. Each record pins its original CAS blob; `provenance.edn` separately
pins the derived fixture. ByteArray is a scalar byte buffer, distinct from an
object Array or ordinary constructor. `get` maps to proof-backed `fget`, so the
native checked getter's out-of-range zero return is not this declaration's contract.
Inventory membership alone does not establish execution or engine support.

Upstream: `src/Init/Data/ByteArray/Basic.lean`, `src/include/lean/lean.h` and
`src/runtime/object.cpp` in
[the pinned repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors; derived material is under
[Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
