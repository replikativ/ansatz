# Original Meta forward declarations and exported implementations

Eight original Lean 4.33.1 rows from commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`: Lean.Meta.whnf, whnfImp, inferType,
inferTypeImp and all four genuine boxed wrappers. Only top-level pretty was
removed. Each record retains the original raw CAS SHA256 and exact typed Name;
provenance.edn pins this serialized fixture and the upstream source files.
The selected rows are not a complete executable body/dependency closure.

The explicit export attributes bind lean_whnf to Lean.Meta.whnfImp and
lean_infer_type to Lean.Meta.inferTypeImp. Their raw ABIs match, including owned
arguments and void world lane; boxed wrapper ABIs have tagged world lanes. The
original base CAS rows have no redirect association, so the source export proof
is distinct from row identity. See
[the binding contract](../../../research/JAVA_GUEST_EXPORT_BINDINGS.md).

Original sources: Lean/Meta/{Basic,WHNF,InferType}.lean and
Lean/Compiler/{ExportAttr,LCNF/EmitC,LCNF/InferBorrow,LCNF/ToDecl,IR/CompilerM}.lean
under src in
[the pinned Lean repository](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6).
Copyright Microsoft Corporation and contributors, under
[Apache License 2.0](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/LICENSE).

Tests stop at authenticated implementation CodeRequests; they do not execute
MetaM with fabricated contexts, replace inference with a host callback, or claim
kernel admission.
