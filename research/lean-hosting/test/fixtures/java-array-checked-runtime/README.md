# Original Lean checked Array getters

The four declarations in `original-rows.json` are `Array.get!Internal`,
`Array.get!InternalBorrowed` and their two genuine boxed wrappers from Lean
4.33.1 at commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

Only optional top-level `pretty` was removed. Bodies, ABIs and other metadata are
unchanged. Each record pins its original CAS blob; `provenance.edn` separately
pins the derived fixture. Borrowed-result getters retain their compiler-only
lifetime contract. An implementation limited to valid in-bounds calls must
explicitly reject the native panic/default path before ownership effects;
returning the default silently is not an equivalent implementation.

Upstream: `src/Init/Prelude.lean`, `src/include/lean/lean.h` and
`src/runtime/object.cpp` in
[the pinned repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors; derived material is under
[Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
