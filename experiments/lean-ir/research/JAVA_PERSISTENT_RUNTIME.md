# Bounded Runtime.markPersistent

The native intrinsic `lean_runtime_mark_persistent` (ID542) follows Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, `src/runtime/io.cpp` and the
`lean_mark_persistent` loop in `src/runtime/object.cpp`. The original declaration
is `Runtime.markPersistent` in `Init/System/IO.lean`. Its exact raw ABI is
`[erased,tobject,void] → tobject`, all owned; the original boxed wrapper has
`[tobject,tobject,tagged] → tobject`, all owned. Fixture files preserve both actual
captured row byte digests and source index provenance.

The operation returns the identical argument with no INC/DEC, allocation counter
change, new pointer identity or new MT marker. Every supported positive-RC owning
node reachable from that argument becomes RC0. Existing RC0 nodes stop traversal,
including a persistent Ref whose payload was replaced after its original mark.
Ordinary constructors, closure captures, live object-array slots, byte arrays,
Ref's present payload and the result of a one-field ready Task are supported.
Long, BigInteger and String values are immutable atomic leaves. Cycles and
sharing use identity tracking; spare Array capacity is not an owning edge.

The port first performs a read-only iterative preflight of at most 300,000 unique
positive-RC Nodes and 1,000,000 owning field occurrences. These limits provide
headroom for the selected roughly230k-node combined Prelude/runtime graph and
remain an explicit capability bound. All source-generation, branch ownership,
liveness, kind, payload extent, interrupt and resource checks precede an rc-only,
nonthrowing commit. No guest calls or publication can observe an intermediate
mark in the existing thread-confined engine. SourceBinding/header provenance and
boxed-wrapper ownership rules continue through existing execution paths.

Runtime-created Task/Promise metadata retains its existing positive-RC lifecycle
policy and fails before any marking. Native pending Task marking can block or
execute `lean_task_get`; this port does neither. External objects requiring
`m_foreach`, native handles and Thunks are unsupported and fail before mutation.
Those are actual capability stops, not successful empty handlers. The existing
Ref.set/Ref.swap policy independently marks later payloads logically MT; it does
not turn those payloads persistent. Fork copies still use the existing shared
memo, preserving RC0, pointer identity provenance, aliases and cycles while
isolating mutable Ref fields. Persistence does not grant executable IR or kernel
checking authority.

`persistent-checks.clj` exercises the exact original raw/boxed declarations,
both drivers, direct/FAP/PAP/AP entry, identity and RC0 no-op, cycles/aliases,
arrays/bytes/Refs/ready Tasks/closure captures, source-bound header paths, mutation
failure atomicity, cancellation, the edge bound, deep iterative traversal and
fork/ref payload policy. The suite is registered in the research check runner.
Compilation is independent of the main Java kernel:

```sh
javac -J-Xmx192m -d target/java-mark-persistent-classes \
  research/java-ir-baseline/src/ansatz/research/ir/Interpreter.java
```

Run the research checks in the root-coordinated retained JVM with a fresh
`java-ir-baseline/class-basis` for that class directory. A loaded interpreter
class is not replaced under an active engine.
