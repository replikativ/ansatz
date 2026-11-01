# Original Lean ST.Ref declarations

The twelve declarations in `original-rows.json` are the six ST ref primitives and
their six genuine compiler-generated owned boxed wrappers, exported from Lean
4.33.1 at commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Only the optional
top-level `pretty` text was removed; bodies, ABIs and other metadata are unchanged.

Each record retains its original exported blob SHA-256. `provenance.edn` pins the
derived fixture bytes separately; these two hashes have different meanings.
The fixture requires no native Lean build to run the JVM regression tests.

Upstream source: `src/Init/System/ST.lean` and `src/runtime/io.cpp` in
[the pinned Lean repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors; derived upstream material is
distributed under [Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
