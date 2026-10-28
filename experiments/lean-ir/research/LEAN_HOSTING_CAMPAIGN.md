# Lean hosting campaign: handoff after branching experiments

## Target and execution model

The target remains loading Lean files, executing them efficiently on the JVM,
and providing practical Clojure/Java-to-Lean and Lean-to-host calls. Persistent
execution state should support explicit branching without requiring persistent
updates or full snapshots inside every closed execution region.

Lean logical RC, physical JVM storage ownership and resource authority are
separate facts. RC1 can justify guest uniqueness but cannot alone prove that
private arrays are unshared with a retained snapshot. A closed region can use
mutable storage and primitive JVM workers; publishing or forking must establish
immutable roots and invalidate any mutation rights inconsistent with sharing.

The proposed execution modes are:

- Existing World-based handlers retain their complete checkpoint contract.
- Scoped, classified effects may keep the machine private between exposed
  suspension, pause, completion or requested capture points.
- Typed closed regions can compile to primitive JVM code, with explicit state
  materialization at exits. A guard failure must either reconstruct that state
  or fall back before effects; it must not replay external effects.

Being unable to fork *inside* a region need not prevent forking before/after it.
A future mid-region capture would require compiler state maps or deoptimization
support. JVM-level speed near native Lean, or an advantage through JIT
specialization, is a target requiring benchmarks, not an established result.

## Evidence already obtained

- [Explicit Java continuations](java-ir-baseline/CONTINUATIONS.md) support
  instruction-boundary pause/resume and 20,000 non-tail guest calls without Java
  guest call frames. Both drivers share the same data/RC model. The isolated jar
  gate passes 26 test executions / 1,331 assertions. Final paired CPU overhead
  was about 25% on default JVMCI and 15–28% across two C2 controls, with equal warm
  allocation. Recursive execution remains the default; heap forking and managed
  cancellation are still separate work.

- The [Java interpreter baseline](java-ir-baseline/README.md) executes original
  typed exported IR with direct node headers, reusable stacks and lexical joins.
  On RBMap1000/1001 it measured 6.16 ms wall with ordinary C2 or 2.82 ms with the
  default JVMCI compiler, versus 4.51 ms for Lean's IR-preferred interpreter.
  Nine tests / 258 assertions cover intermediate values, guest counters and
  ownership, including all 81 MCMC data declarations. This bounded research
  engine is not yet forkable or integrated into the hosted loader. The next
  structural experiment is explicit continuations, followed by branch-local
  heap ownership, each measured independently against this baseline.

- [Prepared native call regions](NATIVE_CALL_REGIONS.md) provide an opt-in
  low-level runner without global interpreter replacement. The bounded paired
  RBMap case measured about 18% less CPU and 21% less allocation, with exact
  checkpoint/fork checks and isolated jar consumption. File-loader defaults and
  current-head full-frontend acceptance remain separate campaign work.

- [Register capture probes](REGISTER_CAPTURE_PROBES.md) retain exact fork and
  checkpoint state with copy-on-write pages. The bounded final RBMap comparison
  saved about 17% cumulative allocation at about 2% more CPU; dense registers
  remain the default. This is a research adapter, not a fourth released backend.

- The [constructor corpus and cache-admission investigation](INTERPRETER_COST_CORPUS.md)
  found repeated hashing and retention of runtime-created continuations in the
  lazy compiler. Source-based admission removes that growth in bounded tests and
  cuts the MH constructor's compiled execution from about 13.0 to 0.58 ms. The
  ordinary interpreter remains faster on that constructor. These raw-IR results
  do not establish hosted file-loading speed or current-head full-image acceptance.

- A historical genuine hosted frontend run at main `01016b2` passed all 17
  stages, including strict checking of 65,994 constants with 15 assumptions,
  edited/retained versions, host callbacks and managed teardown. This is
  historical fixed-cohort evidence, not current-head or general project support.
- Native-exported selected RBMap and unchanged finite MCMC closures had initial
  exact World agreement on the persistent, mutable and JVM backends. That did
  not establish unchanged project file loading on the current cohort.
- PR227 and PR228 landed continuation-layout and unchanged-host private-storage
  improvements with independent review and CI. They preserve immutable handler
  checkpoints; current full-image performance has not been remeasured.
- The [five-step branch experiment](KLARA_BRANCH_RESULTS.md) adds scoped effects,
  isolated guest/host cells, generated Lean closure/RC cleanup, separate owner
  ledger composition and a small proved pure model with finite runtime checks.
  These are experimental adapters, not shipped production interop contracts.

The large frontend/image experiment remains parked while the bounded execution
path is improved. Recent REPL allocation reductions must not be applied as
predicted whole-frontend speedups without measuring actual uptake.

## Landing sequence

1. Land the branching experiment as one additive, reviewed PR. Include sources,
   generated fixture/provenance, model/proofs, measurements, limitations and the
   25-test bounded CI gate. No production default or new runtime dependency.
   CI checks runtime/model observations; native proof verification is a separate
   recorded command, not silently claimed as part of the JVM gate.
2. Specify the production scoped effect ABI: descriptors and capabilities,
   which boundaries expose a World, continuation capture/pause behavior,
   checkpoint/failure semantics, cleanup authority and compatibility fallback.
   Keep code/module basis separate from per-branch runtime handles.
3. Implement that ABI over the existing machine, then connect selected typed
   compiler regions. Use immutable program/layout facts, version guards and
   scalar/typed runtime handles. Preserve the reference backend as an oracle.
   Profile representative generated programs and ordinary host calls in a
   retained small REPL; keep cold preparation distinct from warm execution.
4. Once bounded results justify it, run one fresh complete hosted acceptance
   campaign at the landed head. Compare all backend outputs, retained versions,
   host interop, ownership cleanup and measured time/allocation/heap. Reuse its
   warmed resident state for investigation rather than bootstrapping repeatedly.
5. Expand unchanged Lean project coverage (including MCMC), imports, algebraic
   data and cross-language errors/ownership; finish public Clojure/Java APIs,
   packaging, compatibility documentation and release evidence. Hosting Lean's
   frontend itself remains separate from porting/replacing its kernel or
   proving the runtime correct.

Klara alignment begins with the shared observation/ownership contract and
adapters. Lowering into a future Klara compiler can follow once its target
representations and effect ABI are stable. These experiments do not yet run
the Lean interpreter inside Klara.
