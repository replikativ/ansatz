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

- The [U32/USize slice](JAVA_SCALAR_RUNTIME.md) adds raw word lanes, 64-bit Lean
  boxing/layout, seven captured scalar declarations and 75 native observations
  through direct and guest calls. The 384 MiB isolated jar gate passes 54
  executions / 3,776 assertions. RBMap main has 11 unsupported extern
  declarations; string/array/IO execution is pending.

- The [captured extern ABI and Nat expansion](JAVA_EXTERN_RUNTIME.md) adds exact
  signature/borrow validation and three Nat operations against 288 pinned native
  observations. Both drivers pass the isolated jar gate, now 42 executions /
  2,711 assertions. RBMap main has 18 unsupported extern declarations remaining;
  scalar/data/IO execution and loader integration are still pending.

- The [unchanged-source compatibility corpus](LEAN_COMPATIBILITY_CORPUS.md)
  pins initial application targets and separates raw execution from hosted source
  loading. Its bounded, non-executing inventory covers original RBMap `main`:
  79 reachable declarations, 26 extern declarations, 21 outside the current
  Java preparation profile, and two dynamic application sites. Runtime binding
  coverage and source-loader integration remain explicit acceptance work.

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
  engine is not yet forkable or integrated into the hosted loader. Explicit
  continuations have since landed; branch-local heap ownership remains the next
  structural experiment, measured independently against this baseline. Runtime
  IO coverage can advance separately through the compatibility corpus.

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

The execution order below refines the earlier experimental landing sequence.
The published compatibility corpus, rather than arbitrary Lean/Lake compatibility,
defines the first release boundary. The hosted frontend and eventual rebuilding
of its own compiler artifacts remain later hosting gates.

1. Finish the bounded Java value/runtime profile: U32/USize, boxing and packed
   fields; strings/arrays; host boundaries and valid guest streams. Run original
   RBMap `main` with native observations, errors and pause/ownership checks.
2. Establish branch-local heap ownership and managed completion/failure cleanup,
   preserving the mutable closed-execution control. Define external resource
   sharing/fork behavior explicitly; do not make real IO replay implicit.
3. Integrate the Java tier under existing admitted loader/provider, kernel,
   versioned file handles and Java/Clojure APIs. Preserve trusted registry and
   source/executable association checks. Exercise edits, retained contexts,
   callbacks, failures and isolated package consumption.
   A bounded pure-call slice may precede general heap persistence: retain the
   existing frontend/kernel control plane, select Java code after admission,
   and use per-call private heaps with value-only codecs. No mutable engine,
   cache or escaping Java heap node may be shared by context forks. General
   closures/effects/persistent heaps require their ownership/host-boundary
   contracts.
4. Admit bidirectional DSL/Lean composition **after loader integration and before
   publishing project examples**: load a Lean function/theorem into a DSL
   definition/proof; publish a checked DSL function/theorem for a subsequent
   Lean file. Preserve Names, universes, versions, assumptions and required
   instance/simp metadata. Keep the DSL's existing supported Clojure codegen;
   imported code can use the Lean IR engine behind the same declaration identity.
   Different logical types require conversions; runtime representations require
   codecs as appropriate. This is a pending acceptance gate, not current support.
5. Complete unchanged-source corpus entries, including actual finite MCMC
   execution, checked proof-bearing imports and a manageable IO/import example.
   Publish per-entry versions, observations, unsupported paths and reproduction.
6. Package the bounded preview with explicit bootstrap/provider setup, public
   APIs, ownership/version documentation and clean consumer acceptance. It must
   load and execute the accepted original sources, not only replay raw IR.
7. Complete an in-process hosted Lean frontend invocation with imports,
   initialization, syntax registration, elaboration, checking, diagnostics and
   new callable code. Retire native dependencies for this chosen profile, then
   validate rebuilding the frontend/compiler artifacts inside the JVM. Full Lake,
   arbitrary native plugins and general concurrent-server support are separate.

Each runtime feature is validated in the retained small REPL and against pinned
Lean before a full-image acceptance run. Land independently reviewed, green
increments without collecting a backlog of ready PRs. The original historical
sequence below records how the earlier scoped-branching experiments were landed;
it is not a request to repeat their completed work.

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
