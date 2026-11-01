# Original proof-carrying String position declarations

Eight exact original declarations from Lean 4.33.1 commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`: String.Pos.set, String.decodeChar,
String.Pos.next, String.extract and their four genuine boxed wrappers.

Only top-level pretty was removed; original bodies, dependencies, borrow flags
and raw ABI metadata are unchanged. Each record identifies its original raw CAS
blob with SHA256 and exact typed Name. provenance.edn pins the serialized fixture,
producer index and upstream source files. These selected rows are not a complete
frontend closure.

The modern setter's raw ABI is owned object/tobject/uint32/erased → object;
legacy String.Pos.Raw.set uses owned object, borrowed tobject, uint32 → object
under the same native symbol. Pos erases to a logical Nat byte offset; the native
implementation uses usize only after its representation/range assumptions.
Execute the original boxed wrappers rather than synthesizing ownership adapters.

Source: Init/Data/String/{Defs,Basic,Modify}.lean, src/include/lean/lean.h and
src/runtime/object.cpp in
[the pinned Lean repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation, Lean FRO, LLC and contributors; derived material
is under [Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).
