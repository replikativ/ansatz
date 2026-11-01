# Frontend runtime portability review

Evidence is pinned Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and the local experiment. This is a
runtime-boundary inventory, not a claim that every linked function executes.

A streaming read of `target/frontend-full-world-archive.edn` found 311,523 lowered
functions and 166 distinct deferred extern symbols. Fourteen are now implemented
in the 304-symbol runtime registry captured by this review; none of the remaining
symbols resolves through the 224-entry export alias inventory. The 152 remaining
candidates comprise 103 numeric operations, 17 object/expression operations,
four kernel/generated-declaration operations and 28 host facilities. This archive
predates later source-helper closures and runtime patches. It does not inventory
the current running session, installed raw capabilities or future file imports.
The small generated lists are `target/review-{archived-deferred,unimplemented-externs}.json`.

The most likely semantic gates are expression search/replacement, loose-variable
operations and ordering; UTF8 mutation/conversion; byte-array slicing; and
`shareCommon`. The actual later compiler gate `lean_find_ext_expr` is not in the
historical list. Its three-way callback result and omission of partial application
callbacks differ from simple `find?` ([FindExpr](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Util/FindExpr.lean#L25)).
`replace` needs visible guest callback execution and the native traversal/cache
contract; substituting `replaceNoCache` changes invocation behavior
([ReplaceExpr](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Util/ReplaceExpr.lean#L16)).
Sharing externs are genuine generic object equality/hash/canonicalization
operations, not permission to replace sharing with identity and claim native
pointer/RC behavior ([ShareCommon](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/ShareCommon.lean#L42)).

Kernel boundaries remain distinct. `lean_add_decl` consumes a kernel environment;
it cannot reuse the elaborator-environment adapter blindly. `lean_kernel_check`
accepts an open local context, beyond the current closed-term projection.
`lean_mk_cases_on` generates a declaration and needs an actual construction
algorithm followed by strict admission. Unchecked admission must remain absent
from the default bridge; upstream explicitly calls it unsound
([Environment](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Environment.lean#L299),
[CasesOn](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Meta/Constructions/CasesOn.lean#L15)).

Host facilities include clocks, OS file handles/filesystem/processes, thread/build
queries and TCP. Whole-Lean linkage does not make TCP or native process spawning
necessary for the in-memory file API. Provide explicit capabilities where needed;
never substitute successful empty effects. Existing buffer streams, virtual
verified import regions and pinned build metadata are narrower supported profiles.
The task runtime is cooperative, not native-thread equivalent; unresolved waits
fail explicitly. Mutex allocation alone does not implement lock/unlock, whose
native contract requires ownership and actual waiting
([Mutex](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Std/Sync/Mutex.lean#L31)).

Practical acceptance should be file-specific: native/hosted diagnostics and checked
constants, executable IR plus initialized effects, rollback/fork ownership, and
repeat-file latency after one initialized world. Completed initialization, linked
function counts, supported-symbol counts and parser agreement are different
milestones. None establishes general Lean library, native FFI, concurrency or
cross-platform support. The current scalar/profile limits, explicit runtime traps,
strict signatures, source-inductive subset and native-assisted artifact producer
must stay visible in capability claims.
