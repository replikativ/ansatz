# Cooperative kernel cancellation snapshot

Pinned Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

`kernel_host` now accepts a borrowed `Option IO.CancelToken` through the new
`KernelControlShim.cancellationIsSet` guest helper. That helper calls the actual
`IO.CancelToken.isSet` function, which reads its IO reference. The host does not
duplicate the token's private promise/reference layout. None remains supported
without control helpers. An unset token permits ordinary strict Java checking.

This is a cooperative snapshot contract: the guest scheduler does not execute
another token setter while one synchronous Java checker invocation is running.
Concurrent native token mutation is outside this runtime profile. No native
reference counting or thread-local cancellation pointer is imported.

Cancellation is not unconditionally checked at the native add-declaration
entry. Pinned `kernel/environment.cpp` first checks the declaration name,
duplicate universe parameters, then metavariables/free variables in its type.
`kernel/type_checker.cpp` rejects loose bound variables before its first
`check_system(..., true)` poll. Consequently a set token must not turn these
earlier errors into `.interrupted`.

`KernelControlShim.cancelledSingleResult` mirrors that pre-poll order for axioms,
definitions, theorems and opaques, returning the actual guest
`Except Kernel.Exception Environment` error inside an Option. The successful
preflight path returns the genuine scalar `.interrupted` constructor, not
`.other`. No Java admission or publication occurs in this branch. The owned
input Environment is released exactly once; the borrowed declaration and Option
owners stay intact. Mutual, inductive and quotient set-token pre-poll orders are
explicitly unsupported (None from the helper), rather than guessed. Unset tokens
do not restrict the existing supported declaration kinds.

Native heartbeat accounting, the native recursion-limit factor, memory/stack
exhaustion precedence, and host checker fuel remain separate limits. This slice
does not claim their equivalence.

The source-local helper artifact is `target/kernel-control-shim-source.jsonl`,
14 rows, zero initialization actions, SHA256
`0d3fc3873b8cc4b1ceb4fa8a6bdc34e2ea619c432841ee7c6e10b63e151fa611`.
Exact raw signatures:

| Helper | Inputs | Result |
| --- | --- | --- |
| `KernelControlShim.cancellationIsSet` | borrowed tobject Option; void world | UInt8 Bool (BaseIO, no IO wrapper) |
| `KernelControlShim.cancelledSingleResult` | borrowed object Environment; borrowed tobject Declaration | owned tobject Option(Except) |

`kernel-host/control-helpers` supplies these structured names. The preparation
function in `target/prepare-kernel-controls.clj` loads their closure against an
existing catalogue/program without running guest code or replacing existing
function objects. Merge those helper entries into the existing full helper map
and rebuild the kernel binding with the original policy. Keep the old
KernelBridgeShim source and artifact unchanged.

`lean/KernelControlOracle.lean` compares eleven cases against the real native
kernel: four single declaration kinds, duplicate name and universe parameters,
expression/level metavariables, free and loose bound variables, and an unknown
constant type. It also checks None, a fresh unset token, repeated set, and the
unsupported quotient path. All native comparisons passed; outputs are
`target/kernel-control-native.jsonl` and `.log`.

Focused JVM validation passed eighteen tests and 216 assertions at 256 MB,
including existing kernel-host tests plus
`prototype.kernel-host-cancellation-test`. New tests cover borrowed ownership,
forked set/unset snapshots, correct interrupted/error propagation, no publication
on cancellation, and explicit unsupported/capability failures. Actual hosted
helper invocation remains for resident integration; no resident REPL was edited
by this task.
