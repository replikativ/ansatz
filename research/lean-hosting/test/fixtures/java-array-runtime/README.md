# Original Lean Array declarations

The 28 declarations in `original-rows.json` are fourteen Array operations and
their fourteen genuine compiler-generated boxed wrappers, exported from Lean
4.33.1 at commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Only optional
top-level `pretty` text was removed; bodies, ABIs and other metadata are unchanged.

The operations are `mkEmpty`, `emptyWithCapacity`, `push`, `pop`, `usize`, `uget`,
`ugetBorrowed`, `getInternal`, `getInternalBorrowed`, `set`, `uset`, `swap`,
`toList` and `replicate`. All fourteen original `._boxed` rows were present.
`set` maps to `lean_array_fset`; `swap` maps to `lean_array_fswap`. These are the
proof-backed operations, distinct from the checked C helpers of similar names.

Each record retains its original exported blob SHA-256. `provenance.edn` pins the
derived fixture bytes separately; these hashes have different meanings. The
fixture requires no native Lean build or full producer index to exercise it.
Borrowed-result operations and their original wrappers retain the unsafe,
compiler-directed lifetime contract; these rows do not make that contract safe
for arbitrary host callers.

Upstream sources: `src/Init/Prelude.lean`, `src/Init/Data/Array/Basic.lean`,
`src/include/lean/lean.h` and `src/runtime/object.cpp` in
[the pinned Lean repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors; derived upstream material is
distributed under [Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
