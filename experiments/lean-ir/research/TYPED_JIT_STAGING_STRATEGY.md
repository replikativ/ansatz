# Typed staging and adaptive JVM compilation

Decision record, 2026-10-26. This is a researched direction, not a claim of
complete implementation, formal compiler verification, or native performance.

Use the existing pipeline: canonical Lean IR → validated typed optimization IR
→ represented operations → JVM code. Keep interpretation and generic compiled
blocks available. AOT/prewarming and demand compilation should schedule the
same passes and code emitter; runtime specialization adds facts that were not
available earlier. HotSpot/Graal then compiles the generated JVM methods.
No Truffle dependency or separate execution engine is required for this step.

## Use static information early

| Fact | Lowering opportunity | Dynamic obligation |
| --- | --- | --- |
| Validated scalar signature and direct ABI | Primitive lanes, exact operations and transfer plans | Public carrier and program-version boundaries |
| Known literal, direct callee or constructor layout on a proven path | Constant propagation, direct calls, reduced branches and field planning | Preserve canonical state/cost reconstruction |
| Nat operation and represented nonnegative Long input | Unboxed arithmetic | Entry validation and addition promotion unless a range proof excludes overflow |
| Observed closure target or mutable semantic dependency | Optional bounded specialization | Identity/generation validation and fallback |
| Guest aliasing and storage ownership | Reuse through existing heap operations | Both guest RC and persistent snapshot/COW rules |
| Fuel and current continuation | Execute a complete compiled chunk | Exact prefix, locals, frames and yield recovery |

Known facts need justification from actual installed producer rows, scoped
analysis and exact ABI/semantic dependencies. Neither erased object annotations
nor arbitrary caller metadata prove semantic Nat, layout or ownership. The
compiler analysis itself is not formally proved. Preserve canonical imported
IR separately from its optimization companions and reconstruction recipes.

An initially sufficient partial evaluator propagates known immutable constants
and unknown typed values, with ranges/layout/callee facts added as justified.
Evaluate only a closed set of exact guest operations. Unknown or effectful
operations residualize; compilation must not invoke a host callback or move a
guest exception. Bound rewrite rounds, graph growth, emitted code and constants.

## Lessons from related implementations

Source research inspected Graal `d2e7bd1e957d593e614d240311c4b7a78d983e82`,
Daphne `f68d7041157178f81900d09f002c2af9e58ca12e`, Raster
`1c47d3e3729f402944487c1c78e723fb61a1449b`, and Pattern
`89da31a64f5150a180a1233cd13fa1de4f42e416`. These are inspected checkout
revisions, not automatically the dependencies selected by Ansatz's package.

- Graal's `PEGraphDecoder`, Truffle `PartialEvaluator`, assumptions and virtual
  object/frame state demonstrate bounded residualization, dependency invalidation
  and explicit recovery state. Its compiler directives have compiler-specific
  meaning; copying annotations into ordinary Clojure does not recreate that PE.
  JVM deoptimization recovers Java execution. Ansatz must separately recover
  guest World, locals, ownership and fuel state.
- Daphne's `src/daphne/partial_evaluation.clj` propagates constants, reduces
  conditionals and residualizes applications. Its memoized host `eval` and
  symbol-based knownness are unsuitable as Lean effect or semantic authority.
  Reuse the staging approach with explicit guest operations and finite budgets.
- Raster's scalar PE/effect passes, abstract values and JVM emitter illustrate
  scope-safe propagation, conservative unknown effects, separate logical and
  physical representation, and bounded method splitting. Reuse the organization
  and measured interfaces; do not import its entire backend or tensor model.
- Pattern dialects and nanopasses describe compiler transformations. Grammar
  validation does not replace typing, effects, ownership or admission checks.

Keep the current Clojure form emitter until measurements justify a narrow
bytecode-emission seam. Rich guest adaptation and the host JVM JIT can coexist;
neither implies competitive performance with native Lean without benchmarks.

## Next experiments

1. Attribute the unchanged rbmap workload's generic JVM allocation and calls.
   Its measured n=1000 baseline is about 266 ms CPU and 163 MB host allocation,
   with 35 generic blocks, compared with 304 ms/238 MB mutable. These bounded
   resident samples are not steady state or native-C comparisons. The quotient
   of host allocation by guest steps is not an allocation profile.
2. Select one frequent direct-call/constructor/projection/case pattern from that
   profile. Lower static facts early using existing heap/RC/COW operations.
   Compare unchanged producer IR with the pass on/off; test short fuel prefixes,
   errors, exact carriers, aliasing, retained siblings and caller recovery.
   Keep allocation identities observable before attempting virtualization.
3. In the real-file A/B/A gate, compare demand compilation with explicit
   prewarming. Record preparation, emission, first call, warmed calls,
   cache/version keys, fallback reasons and retained classes separately. Address
   guard cost, code size or emission latency only when the measurements select it.

An edit creates a new immutable code version. Retained A remains callable after
B; share pure artifacts through dependency-complete keys, never owner-bearing
Contexts or leases. Cache/class lifetime needs bounds for a long-running REPL.
Amortizing validation is valid only at an explicit immutable or sealed semantic
boundary; do not silently discard supported Clojure reload/redefinition behavior.

Hosted frontend loading remains a separate workload. Restore, checking,
projection, repeated closure validation and publication can dominate it.
Primitive application speedups do not establish fast loading, and native-exported
IR execution does not establish hosted elaboration of the original files.
