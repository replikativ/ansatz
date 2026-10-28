# Unchanged Lean compatibility corpus

This is the proposed acceptance scope for the Lean-on-JVM preview, not a list
of shipped source-compatible programs. The machine-readable
[manifest](compatibility-corpus.edn) pins source and available raw IR. Paths in
the manifest are relative to `experiments/lean-ir`. Reproducing the inventory
does not need the sibling repositories, a Lean executable or an Init image.

## Acceptance boundary

An accepted entry keeps its original source bytes and module structure. Host
configuration supplies project/dependency roots, pinned versions, checked import
artifacts and explicit runtime bindings. We distinguish importing an existing
checked artifact from rebuilding its source. The preview does not promise
arbitrary `lake build`, build hooks, native libraries or all Mathlib tactics.

For each executable entry, admission requires source loading through the hosted
frontend, checked imports, observations compared with pinned native Lean,
Java/Clojure invocation, and an isolated packaged consumer. Examples with host
callbacks must additionally exercise reverse calls. Fork/version/cleanup checks
apply to the corresponding execution and resource contracts. Raw IR preparation
alone satisfies none of the source-loading requirements.

## Selected scope and current evidence

| Entry | Purpose | Current Java engine evidence | Remaining boundary |
| --- | --- | --- | --- |
| Original Lean RBMap computation | Persistent tree construction, recursion, joins, closures, RC | Complete values and counters; recursive and explicit drivers | Hosted source loading and public interop integration |
| Original RBMap `main` | Arguments, parsing, decimal rendering, stdout | Static inventory only | Wider scalar lanes, strings/arrays/Nat primitives, stream host binding, execution and IO oracle |
| MCMC `CompilerIR.lean` | Original sampler-description algebraic data | All 81 nullary declarations, twice, compared to persistent reference | Hosted source loading; independent native observation gate |
| MCMC `CompilerIRInterpreter.lean` | Actual finite categorical/MH execution | Pending capture and execution | Transitive dependency/runtime audit and finite draw-trace comparison |
| MCMC `TwoState.lean` | Imported proof-bearing application module | Pending | Mathlib import/tactic/`native_decide` compatibility and checked loading |
| Small multi-file IO example | Project imports, files, errors and REPL edits | Candidate not selected | Pin a manageable original example after the IO runtime audit |

The MCMC checkout at the pinned revision uses Lean/Mathlib 4.33.1, matching the
producer. Version agreement is not a compatibility result. MCMC's `CompilerIR`
is its sampler DSL, not Lean's compiler implementation. Executing constructor
data does not execute a sampler or host Lean's frontend. The Julia application
runtime in that repository is outside this Lean corpus.

## Non-executing inventory

Load `java-ir-baseline/corpus.clj` in the retained REPL after the existing
`java-ir-baseline/repl.clj` adapter, then run:

```clojure
(def corpus-basis
  (java-ir-baseline/class-basis "target/java-ir-continuations/interpreter.jar"))
(lean-compatibility-corpus/audit corpus-basis "research/compatibility-corpus.edn")
```

A standalone optional invocation, after building the engine jar as described in
its [README](java-ir-baseline/README.md):

```sh
clojure -J-Xmx384m -J-Xss8m -M research/java-ir-baseline/corpus-runner.clj \
  target/java-ir-baseline/interpreter.jar target/compatibility-inventory.edn
```

The audit verifies local fixture hashes, derives static `fap`/`pap` edges from
actual bodies and follows initializer/redirect identities. It asks the real Java
preparer about each extern separately, obtaining all extern blockers without
duplicating a runtime whitelist. Full-closure preparation remains a distinct
result and can expose instruction/type blockers beyond externs. Original export
dependency metadata is not substituted for body inspection.
Each captured artifact must have exactly one manifest and the pinned Lean
version. Producer revision is attested by original capture provenance and
artifact hashes; the IR manifest does not encode the Git revision. Source paths
without a vendored fixture are planned identities, not locally verified bytes.
Row initializer/redirect links are inventoried, but Java preparation does not
implement or validate their runtime semantics.

The [recorded inventory](../measurements/compatibility-corpus-2026-10-28.edn)
finds 79 declarations reachable from RBMap's `main`, including 26 extern
declarations, of which 21 fail current preparation. Two distinct declaration
signatures name `lean_usize_of_nat`; declaration counts are not symbol counts.
There are two dynamic application sites. In particular, `IO.getStdout` supplies
an `FS.Stream` containing closures: its implementation and closure targets need
their own binding validation, not just static reachability. Module initialization
plans are reported, not executed by this tool.

That original receipt records the first five-Nat-operation engine. The subsequent
[extern expansion](JAVA_EXTERN_RUNTIME.md) implements multiplication, division
and power, reducing unsupported extern declarations from 21 to 18. The original
receipt is retained as historical evidence rather than overwritten.

## Cross-syntax acceptance

The shared logical declaration model should let Lean files and the Ansatz DSL
use one another's checked functions and theorems. Make this an explicit gate:
load a Lean function/theorem, use them in a DSL definition/proof, then publish
a DSL function/theorem for a subsequent Lean file to consume. Recheck admitted
declarations in the target environment; preserve structural Names, universes,
reducibility, declaration/version identity and required instance/simp metadata.
Execution additionally requires an association with matching compiled code.
Different syntax for the same type needs no logical conversion; distinct types
need explicit conversions/equivalences, and JVM values need codecs. Arbitrary
Clojure functions remain declared host bindings, not transparent logical axioms.
This bidirectional session integration is planned, not established by raw IR
execution or kernel compatibility alone.

The existing native capture exported 80 declarations from roots `mkMap`, `fold`
and `main`. The new `rbmap-main.jsonl` fixture preserves that complete capture
verbatim; the main-only inventory omits one unreachable declaration. No new
native export or heavy image experiment was required. Its original capture
provenance remains in
[rbmap-capture.json](../test/fixtures/unchanged-programs/rbmap-capture.json).

## Runtime and hosting sequence

1. Implement the bounded first profile from the
   [IO ABI/resource audit](JAVA_IO_RUNTIME_PLAN.md), using existing Ansatz
   bindings. Specify unsupported operations and effects at fork boundaries
   explicitly.
2. Add the scalar and data primitives needed by original RBMap `main`, followed
   by the stdout stream binding. Validate original-main observations and errors
   against Lean in both Java execution drivers. Retain the computational
   benchmark to detect runtime regressions.
3. Capture finite categorical/MH executable closures and compare deterministic
   draw traces, including errors and remaining trace. Expand the shared runtime
   only where those real closures require it.
4. Connect the Java execution tier to the existing loader/provider, kernel
   admission and public Java/Clojure facade. Reuse existing version/ownership
   contracts rather than introduce a second public loader or host-call stack.
5. Admit selected sources and imports from this corpus through that integrated
   path. Only then promote individual entries to source-compatible examples.
6. Host a minimal Lean frontend invocation; expand its dependency closure and
   eventually rebuild its own artifacts inside the JVM.

The frontend milestone executes Lean's existing parser, elaborator and compiler
on our runtime. Bootstrap artifacts may initially be generated externally; new
source loading should then run in-process. Compiler self-hosting adds the ability
to rebuild those frontend/compiler artifacts. Ansatz kernel admission remains a
separate authority; execution of a compiler does not itself establish proof
checking. LLVM is unnecessary for either milestone.
