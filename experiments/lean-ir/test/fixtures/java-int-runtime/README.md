# Original Lean logical Int declarations (candidate)

The eighteen declarations in `original-rows.json` are `Int.ofNat`, `negSucc`,
`neg`, `natAbs`, `add`, `sub`, `decEq`, `decLt`, `decLe` and all nine genuine
boxed wrappers from Lean 4.33.1 at commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

Only optional top-level `pretty` was removed; bodies, ABIs and other metadata are
unchanged. Each record pins its original CAS blob; `provenance.edn` separately
pins the candidate fixture. This ignored candidate was extracted without a JVM
and does not establish engine support. Division and bitwise operations are not
part of this tranche.

A Java logical Int carrier may be a signed Long or BigInteger, with exact
arbitrary-precision arithmetic. This does not reproduce native Int allocation,
tagging or physical pointer identity. Nat inputs must remain nonnegative;
owned Nat conversions differ from borrowed signed-Int operations.

Upstream: `src/Init/Prelude.lean`, `src/include/lean/lean.h` and
`src/runtime/object.cpp` in
[the pinned repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors; derived material is under
[Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
