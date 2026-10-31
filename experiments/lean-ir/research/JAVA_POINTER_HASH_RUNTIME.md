# Bounded FoldConsts virtual pointer hashes

The interpreter retains its default local pointer-equality profile and adds an
explicit source-cohort pointer-hash policy. A separate immutable certificate
recognizes only direct pointer USIZE → reserved USize.toUInt64 → reserved mixHash
with a dominating direct U64 literal11. Every use of raw and converted values,
including unreachable joins/alternatives, is audited. Converted/raw words cannot
return, box, store, transfer through joins, capture or escape to arbitrary calls.
The mixed U64 result is ordinary data. This is a deliberate identity-derived
observation, with no secrecy, native address or numeric-hash equivalence claim.

PreparedBody binds actual caller Function and site identity. A complete canonical
three-Header PointerHashPolicy binds the original FoldConsts contains, insert and
expansion functions under one SourceBinding. Ordinary kind, typed Name, raw ABI,
borrow flags, parameter IDs, source hash and no-initializer metadata all matter;
matching descriptive hashes alone do not authenticate source bytes. Configure it
once at an open idle boundary with `PointerHashPolicy.originalFoldConsts` and
`configurePointerHashes`, or the corresponding research facade wrappers.

Preparation recognizes valid hash syntax without granting execution permission.
Prepared body entry checks policy before instructions, including root, FAP/AP and
both drivers. Code reply checks before claiming the pending activation; the
CodeRequest may already own arguments under its existing handoff contract. The
pointer site rechecks actual caller, current Program/PreparedBody and exact site/
target/argument-array identity before accepting a live Expr-shaped Node and
stamping metadata. General body-entry rejection is distinct from first-site
failure after earlier instructions. Raw root/AP/PAP/closure/Host pointer fences
and local equality semantics remain their existing contracts.

The source input contract is bounded: original FoldConsts starts with its
original empty seed and builds this backend's visited table. Trusted source/image
admission establishes that contract; no `verified=true` flag or universal scan of
untyped maps is introduced. Arbitrary imported prebucketed native maps are outside
scope. Imported Expr keys in fresh maps and same-memo forks of target-built tables
are supported by the existing stable aligned virtual word and branch owner.
Fork shares immutable policy, copies table/key aliases with their words and
retargets metadata owners. No Node field, weak identity registry, native ID,
scalar lane, callback action or extra guest ownership is added.

The original empty seed, table arithmetic, collisions/equality, expansion,
traversal and Name dedup all remain original IR. Hash bucket layout does not
order FoldConsts traversal. Structurally equal distinct Expr allocations are
separate pointer keys; constant Names have their independent deduplication.
No arbitrary PtrMap import/rehash or native pointer FFI compatibility follows.

Source review cleared Java SHA
`3791923059497901b5a80c4a6b5fd413e24557d668ef6791f6a0b19c19e3d534`
before execution. Parent retained JVM observations passed the first five tests /
173 assertions in EACH driver, zero failures/errors, on immutable Java11 jar
`50e104db564add252873a203e16203a8f930d3ef0125dd88a5aa544840e9840a`.
Those cases cover default-off/unauthorized entry without stamps, actual original
fresh seed, alias/distinct/duplicate inserts, 144-key expansion, original
getUsedConstants order/Name dedup and repeated empty-seed reuse. Receipt
`target/java-pointer-hash-runtime-v1/focused-v1.out` has SHA
`22115f64eb0f0aefc1149c8c570cb251712afcd7f6351de214c11cd17b1ab781`.

The parent also ran pinned official Lean `--run` on oracle source
`f127e506f03546a1a69293cb9dd5a0061d971e1694dcde9eccee2757e9bbfa23`:
exit0, empty stderr, fifteen stdout lines SHA
`10b0cecbbe7b456c90d51da1cbc116d644da720f350910664cbe76b0d0f7d7c4`.
Only callback order/content and repeated semantic results are compared; no
physical identity or numeric hash output is a golden. The author used bounded
Java11 compilation and metadata/file audits, with no JVM/native test execution
or full image load. Certification/control/fork stress tests and the combined
integration gate are recorded separately when available; this unit alone does
not establish theorem or complete frontend support.
