# Original Lean ready Task declarations

The four declarations in `original-rows.json` are `Task.pure`, `Task.get` and
their two genuine boxed wrappers, exported from Lean 4.33.1 at commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

Only optional top-level `pretty` was removed. Bodies, ABIs and other metadata are
unchanged. Each record pins the original CAS blob; `provenance.edn` separately
pins the derived fixture. These rows support bounded ready-value semantics;
they do not establish support for pending tasks, Task.map, a scheduler or native
task imports. Task.get consumes its Task and returns an owned result.

Upstream: `src/Init/Core.lean`, `src/include/lean/lean.h` and
`src/runtime/object.cpp` in
[the pinned repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors; derived material is under
[Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
