# Original Lean initialization-state query

The two declarations in `original-rows.json` are `IO.initializing` and its
genuine boxed wrapper from Lean 4.33.1 at commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

Only optional top-level `pretty` was removed. Bodies, ABIs and other metadata are
unchanged. Each record pins its original CAS blob; `provenance.edn` separately
pins the derived fixture. The primitive queries runtime boot initialization,
which is separate from guest module-initializer registries and Lean's importing
flag. This fixture does not attest that a prepared graph completed initialization.
No synthetic mark-end or phase-control declaration was added.

Upstream: `src/Init/System/IO.lean`, `src/runtime/io.cpp` and
`src/Lean/ImportingFlag.lean` in
[the pinned repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors; derived material is under
[Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
