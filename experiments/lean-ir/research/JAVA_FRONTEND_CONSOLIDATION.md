# Java frontend consolidation

Campaign decision, 2026-10-29: prioritize the shared Java interpreter as the
execution runtime for a usable hosted Lean REPL. The accepted legacy provider
remains a correctness oracle and source of runtime contracts. Improving its
eager startup is no longer a separate prerequisite campaign.

## Reuse prepared kernel stores

`ansatz.export.storage/load-env` already opens a lazy persistent-store-backed
Java Env. Named Init/Mathlib loading does not recheck every declaration;
normal proving sessions also omit most theorem bodies. Reuse that machinery
and compatible prepared contents rather than eagerly reconstructing all CIs.
Store opening time and cold library/class loading are separate measurements.

Kernel stores supply logical declarations and derived Ansatz metadata. They
do not themselves supply Lean frontend executable IR, all native environment
extension state, runtime constants or module-initialization registrations.
The frontend needs those companions, selected lazily where possible. Run
necessary initialization once per provider, or restore a compatible prepared
state; do not replay the imported proofs or initialize everything per REPL form.

The native guest declaration map and Java kernel Env still need compatible
cohort/name/reference correspondence. Preserve that invariant lazily. A matching
Lean version alone does not establish that two store/export selections agree.
The tiny lazy-base experiment is useful bridge research, not the main product
architecture or a reason to delay Java frontend execution.

## One execution engine and on-demand forks

Keep the Java engine's shared Program/value/heap/extern semantics. Its recursive
and explicit-continuation drivers are execution strategies, not separate public
interpreters. Use the explicit driver for resumable frontend execution.

Existing `eagerFork` copies only when requested, at an idle/completed or explicit
instruction boundary. Ordinary execution remains mutable. Keep this as the v1
fork contract; do not require a persistent ID table or header/payload COW before
frontend support. Capture must include all owning host handles, constant roots,
continuations and mutable provider state. Immutable code and validated immutable
import data may be shared under their actual lifetime contracts.

The current implementation is thread-confined and requires explicit safe-point
control. A concurrent fork request must rendezvous with that control, not copy
an active Java stack or interrupt an external effect. Real resources require an
explicit share/copy/reject policy. Large-frontend capture latency and memory
remain unmeasured; evaluate them after one frontend slice runs. Optimize capture
only if those measurements justify it.

## Next acceptance sequence

1. Map one frontend invocation and its reachable runtime dependencies against
   pinned Lean source. Audit IR preparation/linking, host suspension, globals/
   constants, initialization and runtime value carriers; do not implement every
   extern speculatively. Start with the original `RuntimeCompileShim.inspectFileHeader`
   path, then one Nat definition through `compileImportedFileState`, checking,
   publication and invocation. Header inspection alone is not elaboration.
2. Implement the required Java runtime/bridge slice behind the existing loading
   facade. Reuse store, source, kernel, helper and lifecycle contracts without
   round-tripping the entire guest heap through the legacy World per call.
   Resolve typed host suspension/completion and immutable code-generation identity
   explicitly: the current fixed Program cannot simply be replaced under live
   closures/constants when `evalConst` links new IR.
3. In one retained small test REPL, load a Lean source string, elaborate/check
   it and call the new declaration through the Java runtime. Distinguish code
   preparation, initialization, elaboration, checking and invocation metrics.
4. Retain the provider through edits and calls. Fork at a supported boundary;
   check parent/child isolation, original version retention, constants/refs,
   captured output and host-handle ownership. Define pause/close/failure rules
   before extending to general resources or cancellation.
5. Publish a modest compatibility corpus and one coherent REPL/interop facade.
   Retire superseded execution paths after differential gates pass. A broader
   self-hosting or full Mathlib frontend claim needs separate evidence.

Prefer bounded captured-IR/runtime probes and the retained REPL. Another full
legacy frontend restore is not required merely to start this work. A large-image
run needs a concrete Java integration hypothesis and a bounded resource plan.
