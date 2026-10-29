# Eager Java fork oracle

The shared Java engine now offers `eagerFork(Object[] externalRoots)` returning
a child engine and remapped roots. This is a research correctness control for
the [branch-store design](JAVA_PERSISTENT_HEAP_PLAN.md), not cheap persistent
forking or a new interpreter. Recursive and explicit drivers share the same
value, heap, extern and copying implementation.

Forking accepts idle/completed engines and explicit instruction boundaries between
`advance` calls. It rejects closed, failed, advancing and recursive-active
engines. Engines remain thread-confined; these checks do not supply concurrent
thread safety or Java-frame capture.

One identity map spans nodes, field/root arrays, constants, continuations and
surplus argument arrays. It preserves cycles, duplicate edges, cross-root and
cache aliases, live RC0 descendants and stale dead register aliases. Primitive
stacks/scalar payloads are copied; immutable Program/Body/ordinary function code
is shared. Readiness bits, pending result ownership, phase, counters, limits,
register/join ranges and private output are preserved. Private stream closures,
including partial applications, are rebound to the child owner; foreign-owner
guards remain active.

RC counts are copied without retain operations. Root arrays remap identities;
they create no new guest ownership credits. The caller must account for every
external owner credit associated with the copied graph, including incoming
aliases, not merely the roots it wants to use. Stale registers are not an owner
ledger and cannot prove completeness. Returned handles denote child objects;
old handles still denote the parent. External primitive-array aliases are outside
the root profile: pass owning guest Nodes, not their exposed scalar arrays or
reflected primitive stacks.

Copying costs O(allocated control capacity + graph reachable through copied
roots), including stale control aliases. The engine is not changed on copy
failure. This does not implement general failed-frame disposal or reconstruct
missing external owners. Error-only tracking prevents forking recursive/root
intrinsic states whose failures were not represented by the explicit phase.

## Verification and next step

Thirteen focused tests cover cache/root aliases; readiness false and true;
sixty-four prefixes through mixed calls and application; independent pending
results, arrays and output; cycles; private stream partial applications surviving
parent close; stale dead aliases; a 5,000-node iterative graph copy; RC0 live
descendants; unsupported-root rejection and parent usability; and invalid phases.
The combined isolated engine gate has 109 executions / 10,908 assertions in
384 MiB. No large provider restore is needed for these checks.

The [measurement receipt](../measurements/java-ir-eager-fork-2026-10-28.edn)
records a 5,000-node capture near 1.08 ms CPU and 810,552 allocated bytes, with
child release/close outside timing. A paired RBMap control measured recursive
2.828/2.765 ms and explicit 3.536/3.578 ms CPU (prior/fork-capable engine), with
identical allocation near 1.516 MB per execution. These bounded observations
separate eager capture cost from unchanged ordinary execution; they are not a
general workload or cheap-fork performance claim.

Next compare this eager oracle with stable logical identities and branch versions,
separate header/payload COW and owner-epoch fast paths. Publication must revoke
mutation rights in parent and child. A complete ownership packet/disposal ledger
is needed before general cancellation, resource-bearing captures or durable
snapshot promises. Keep the current mutable closed-call path as the performance
control and measure capture separately from ordinary execution.
