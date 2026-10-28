# Constructor corpus and code-cache admission

This extends the [prepared interpreter probes](PREPARED_INTERPRETER_PROBES.md)
with the four original MCMC CompilerIR constructor roots. They build sampler DSL
data; they do not execute a sampler, load source files, run the hosted frontend,
or check proofs. The existing fixture README pins the native exporter and source.

## Structural finding

The mutable runtime constructs publication continuations during global and IO
initialization. Closure overapplication also constructs continuations containing
surplus guest values. These are execution state, not new program declarations.

Previously lazy compilation visited, fingerprinted and retained every new body
identity. On ten repeated fresh MH-constructor executions, the compiled block
count stayed fixed but identity entries and fingerprint misses each grew by 560.
JFR showed fingerprinting on the execution path despite warmup. Increasing the
compilation threshold or interning publishers would not establish which bodies
are code, and would not solve surplus-value retention generally.

The default lazy runtime now admits only source instruction identities, before
any hint lookup, visit counting, fingerprint or cache write:

1. Build a program-scoped identity index through known syntactic instruction
   edges. Never walk literals, operands or arbitrary/custom containers; unknown
   operators remain inert during discovery. Discovery does not validate unused
   declarations or advance their errors.
2. Interpret unrecognized PCs for one exact ordinary step, with no negative
   cache entry. This includes synthesized publishers, surplus frames and copied
   continuation bodies without known provenance.
3. All runtime-compiled blocks carry their original `:source-body`. After existing
   key/options/arity/extension validation accepts a cached block, admit that
   source subtree before executing it. This preserves continuation identities
   emitted by code reused from an independently parsed equivalent program.

Snapshots, RC, host effects, fuel and the kernel boundary are unchanged. This is
cache admission, not proof of code correctness. The source-root field deliberately
retains static source subtrees. The index is linear in current/adopted source
graphs; shared caches still retain static program versions and are not globally
memory-capped. This does not promise arbitrary host objects can be forked.

## Measured execution

Retained JVM: Java 25.0.1, Clojure 1.12.4, 384 MiB maximum heap. Eight warmups per
mode/root; seven samples, each batching 20 independent machines. Thaw, execution,
and freeze are measured separately using current-thread CPU/allocation counters.
Every completed World is compared with the persistent reference outside timing.
The following are medians divided by 20, per complete constructor invocation:

| MH constructor | Execution CPU | Cumulative execution allocation |
| --- | ---: | ---: |
| Prior lazy compiler | 13.046 ms | 2,697,195 B |
| Source-admitting lazy compiler | 0.582 ms | 611,555 B |
| Ordinary interpreter, final comparison | 0.507 ms | 652,523 B |

This reduces CPU time by a factor of about 22 and allocation by 77% **relative to
the bad prior compiled path**. It is not a Lean-wide speedup. The corrected compiler
still loses to the ordinary interpreter on these short constructor workloads.
Prepared generic lets were also slower on this corpus, despite modest allocation
savings; specialized Nat sites provide no benefit because these roots have none.
Do not switch all execution to the prepared tier based on the RBMap result.

After all four roots warmed, ten further fresh MH executions left all table sizes
unchanged: 257 identity-dispatch/identity-key/visit entries, 211 content-cache and
dispatch blocks, and 484 admitted source identities. The prototype's additional
static filter is retained as a historical diagnostic; production admission also
handles adopted cached-source identities.

One warmed preparation sample for 162 lowered functions measured 0.154 ms CPU and
281,144 allocated bytes to open the program. Indexing alone measured 0.080 ms and
278,336 allocated bytes. These are single warmed samples, not retained index sizes
or predictions for the full frontend image. Full-image startup/index cost remains
unmeasured. Baseline and final runs have different JIT histories; preparation,
measurement setup and whole-process memory are not included in execution figures.

Raw phase samples, cache observations, preparation and profile summaries are in
[interpreter-cost-corpus.edn](../measurements/interpreter-cost-corpus.edn).

## Remaining interpreter work

A separate JFR recording of ten ordinary mutable RBMap size-300 build/fold runs
measured 466,677,984 cumulative thread-allocation bytes, with 220 allocation and
140 execution samples. Sampled allocations pointed to register-array capture at
joins, operand `mapv` calls, and jump/call machinery. Object arrays had the largest
sampled class weight. JFR weights are diagnostic, not exact allocation percentages
or retained-heap measurements.

This strengthens the case for control-flow/frame work before replacing IR maps.
Sparse join materialization already had a CPU regression in the earlier
[bulk probes](BULK_EXECUTION_PROBES.md); do not silently repeat it as a default fix.
Try fixed-arity call/jump preparation and quantify capture cost, preserving
simultaneous argument reads, exact exposed locals, explicit PC/fuel and COW at
actual branch boundaries. Typed compilation remains needed for primitive loops.

## Validation and reproduction

The fresh 384 MiB regression gate passed 126 tests and 27,064 assertions across
lazy runtime, typed compiler, compiled boundaries/versions, coherent selection,
closures and globals. Tests cover all fuel prefixes for synthesized global/IO
publishers and surplus Ref continuations, stable cache/index sizes, no hashing
of generated publishers or surplus guest data, A/B cached multi-region source
adoption, copied-PC fallback, literal exclusion and deferred custom-operator
hashing. Independent source review found no remaining blocker.

An initial retained gate had one instrumentation-count failure after reloading
`lazy/run!`: the unchanged-host storage guard correctly withdrew private reuse
because its captured function identity had changed. A fresh process with coherent
definition owners passed. No runtime guard was weakened to conceal this result.

Load the existing benchmark/prepared research namespaces, then
`static-code-dispatch.clj` and `interpreter-cost-corpus.clj` in the retained REPL.
Create the existing compiler-ir fixture context and call
`interpreter-cost-corpus/probe` with seven trials and batch size 20. The probe
does not reload runtime classes or launch an external Lean process. Do not reload
existing Machine/Ref classes. No full Init/frontend acceptance campaign was run.
