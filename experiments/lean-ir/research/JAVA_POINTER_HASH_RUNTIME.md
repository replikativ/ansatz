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

The separate six-test control suite passed in both drivers on unchanged
`37919230…` / `50e104db…`: recursive64 assertions, explicit76, zero failures or
errors. It covers thirteen full-body certificate adversaries, canonical source/
typed private-number Name/ABI/borrow/once gates, exact caller/site/argument-array
binding, populated-table fork, Code-reply preclaim and in-flight pointer/conversion
fork. Receipt `target/java-pointer-hash-runtime-v1/control-v1.out` has SHA
`b92094c5d738289d8fc8ad3483f1c6d7889a2d46b65f9bd0a603635dec877579`.

The parent additionally passed a preliminary consolidated artifact including the
pointer source and concurrent runtime/private units: source `d29ee127…`, jar
`439b902…`, 128 groups / 1,286 test executions / 55,709 assertions at384 MiB,
exit0. This is separate integration evidence; the final count-guarded pointer
runner wiring and any later controls still require the final combined gate.
This branch adds six groups (5/5/6/6/4/4) after legacy pointer checks and loads them
after their Expr machinery dependency. The local runner has126 groups on its
PR335 base; concurrent branch counts can differ after integration.

The oracle fixture's `verify-oracle.py` checks hard-pinned source/stdout hashes
and an optional newly observed stdout file. It never executes a compiler or
rewrites goldens. The author ran this file check and repository diff/path audits;
all runtime/native observations above were supplied by the parent.

The four follow-on cases passed on the same frozen source and jar in both
drivers: recursive 137 assertions and explicit 159, zero failures/errors. They
compare all fifteen observed native-oracle lines with original JVM FoldConsts
and getUsedConstants calls, suspend/fork a callback through Code and Host, fork
original rehash of a populated map, and exercise guaranteed bucket collisions.
The callback body and collision selection are explicitly research models; the
table operations and hash bodies remain the authenticated original rows.
Receipt: `target/java-pointer-hash-runtime-v1/followup-v1.out`, SHA
`cccc7fdabc54040896959ca6d0ba71c7d2bcf6aa8c694568d0a5122304bc5551`. No Java change or native numeric-hash golden was introduced.

## Consolidated validation

The source-cohort implementation integrates on main14d4afbc with Java SHA-256
`cd52faa0eaee19134fd78c32ae775ed69885cb9424a2b8ece9c43a411fa590b3`
and immutable jar SHA-256
`2475a8956a6d11f3c9a861cc264618a2332acff14112d2b4bc51012eb7239551`.
The 384 MiB combined gate passed129 groups,1,287 tests and56,084 assertions
with exit0, no failures/errors. The later four-test original-callback/expansion
follow-on passed on that same artifact in both drivers (137/159 assertions).
Its two groups are included in the final131-group runner.

The complete runtime integration with the separately reviewed Expr native also
passed the same pointer follow-on on Java94f128fd / jar5aeba892. The original
frontend then processed two axioms and two dependent theorems through strict
Java kernel checks to EOF, with full successful cleanup. That broader acceptance
requires both runtime units; this pointer profile alone is not general frontend
support. No Java kernel source was changed. End-to-end performance impact has
not been benchmarked; the cold frontend receipt includes lazy code loading.
