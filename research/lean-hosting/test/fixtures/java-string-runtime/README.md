# Original Lean String and position declarations

The 62 declarations in `original-rows.json` are 31 String/Substring extern
operations from the original header static inventory and all 31 genuine
compiler-generated boxed wrappers. They were exported from Lean 4.33.1 at commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Only optional top-level `pretty`
text was removed; bodies, ABIs and other metadata are unchanged.

The bounded group covers byte size/access, raw UTF-8 positions (safe and fast
get/next, prev, atEnd, isValid, extract, set), string equality/order/hash,
substring equality, append/push/pushn, contains, list conversion, character
length and position search/conversion. Selection records inventory membership,
not a claim that all operations execute during header parsing or that the Java
engine supports all of them. In particular, `String.hash` has a `uint64` result.

Each record retains its original exported blob SHA-256. `provenance.edn` pins the
derived fixture bytes separately; these hashes have different meanings. Safe
position operations have defined out-of-range behavior that differs from Java
UTF-16 indexing; fast operations retain their proof-backed preconditions.
The fixture requires no native Lean build or full producer catalogue to read.

Upstream sources: `src/include/lean/lean.h`, `src/runtime/object.cpp`,
`src/runtime/hash.cpp` and `src/Init/Data/String/` in
[the pinned Lean repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors; derived upstream material is
distributed under [Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
