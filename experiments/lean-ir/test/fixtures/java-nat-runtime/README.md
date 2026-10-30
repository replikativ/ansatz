# Original Lean Nat comparison and bit declarations

The ten declarations in `original-rows.json` are `Nat.decLe`, `Nat.log2`,
`Nat.lor`, `Nat.shiftLeft`, `Nat.shiftRight` and their five genuine boxed wrappers
from Lean 4.33.1 at commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
These are the remaining Nat comparison/bit operations in the original header
extern inventory. Other Nat operations already covered by the engine are not
repeated here; `Int.natAbs` and `Int.ofNat` belong to a separate Int tranche.

Only optional top-level `pretty` was removed. Bodies, ABIs and other metadata are
unchanged. Each record pins the original CAS blob; `provenance.edn` separately
pins the derived fixture. Inventory membership does not establish execution or
engine support. Large shift amounts require checked resource handling.

Upstream: `src/Init/Prelude.lean`, `src/Init/Data/Nat/Bitwise/Basic.lean`,
`src/include/lean/lean.h`, `src/runtime/object.cpp` in
[the pinned repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors; derived material is under
[Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
