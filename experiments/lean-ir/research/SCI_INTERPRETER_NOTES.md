# SCI interpreter transfer study

Source inspected: sibling SCI checkout, revision
`0d38f0c95338cbf03c82d96ab5943ab07821d4f4` (2026-10-23).
Locators below are relative to that checkout and intentionally portable.
This study ran no JVM or benchmarks; quoted performance observations belong
to SCI's own historical ADRs and do not predict Ansatz results.

## Implemented research boundary

`research/prepared-interpreter.clj` is a host-side prepared **one-instruction**
interpreter experiment, not a replacement runtime. Load once; never reload
`prototype.mutable` or its Machine class to use it.

```clojure
(load-file "research/prepared-interpreter.clj")
(def prepared (prepared-interpreter/prepare-program functions))
(select-keys prepared [:prepared-lets :visited-bodies :preparation-ns])
(prepared-interpreter/run! prepared mutable-machine fuel)
```

Preparation visits only vector bodies reachable through known static function
body positions. It never follows literal payloads or dynamically generated
continuations. A program owns a read-only-after-preparation identity table;
the table, executable nodes and measurements never enter guest snapshots.
Machine `:functions` must be identical to the prepared program's functions.
Restored/copied body identities fall back without growing a dynamic code cache.

Only `:let` with literal/project/scalar-get/ctor/runtime/prim expressions is
prepared. Named protocol/deftype nodes capture operand slots, constants and
continuations. Arguments of arities zero through three use direct vector
construction; higher arities use mapv. Canonical `:body` and one-step charging
remain current. Unsupported instructions use the current `u/step!`.

Every prepared step checks definition-owner roots from
`prototype.mutable/scalar-wrapper-roots`: step, expr, value, ctl and bump.
Changed roots force current `u/step!`; preparation never learns a temporarily
redefined function as its baseline. Private helpers are resolved as Vars,
and helper calls continue observing their roots. Production integration must
consider direct-linking separately; this research assumes ordinary Var-linked
loading, matching the experiment sources.

Primitive execution deliberately calls the current `m/scalar`. All operands
are evaluated before input validation. This retains validation order, dynamic
scalar/small-integer hooks and accepted carriers. Fusing these functions needs
a definition-owned baseline that the current scalar owner does not provide.
There is no runtime eval per guest program and no recursive guest call stack.

Parent-run prefix/fork/dynamic-hook tests and timing are required before any
claim that the experiment preserves behavior or improves performance.

## Transferable source mechanisms

* `src/sci/impl/types.cljc`, `Eval`, `BindingNode`, `ConstantNode`, `->Node`:
  dense object-array slots; named local nodes; other nodes reify Eval. Instances
  at a construction site share that site's generated class. A global Eval
  site can nevertheless become megamorphic: protocols alone promise no win.
* `src/sci/impl/analyzer.cljc`, `gen-return-call`: preparation chooses all-slot,
  slot/constant, or general-expression operand paths. Known arithmetic becomes
  static Numbers calls, avoiding IFn dispatch while retaining boxed operands.
  Current fusion is arities one and two; current tables include equals/get.
* `src/sci/impl/fns.cljc`, `gen-fn`, and analyzer `gen-return-recur`: fixed
  arities avoid generic argument loops. Invocation allocates its binding array;
  recur reuses it. All recur values are read before binding writes.
* Analyzer `DirectVarNode`/`VarNode`, and `src/sci/impl/execution.cljc`: direct
  roots and dense active-world slots have separate paths. Forkable functions
  select an active context; ordinary functions avoid that machinery.
* `src/sci/impl/interop.cljc`, `invoke-static-method-cached`: resolved-method
  cache entries are guarded by argument classes. Reflection, argument arrays,
  adaptation and authority remain costs, not automatically erased by caching.

## Current code versus proposed ADRs

`doc/ai/adr/0006-fused-binding-nodes/README.md` records fused slots/constants
and arithmetic specialization. It also records rejected object-register VM
experiments and a narrow primitive-long VM prototype. Its warmed JVM tree
walker beat the VM variants; native-image results differed. This is a reason
to measure actual dispatch/boxing behavior rather than copying an opcode VM.

`doc/ai/adr/0009-call-node-specialization/README.md` is **Proposed**. Its extended
tables, arity-three specialization, general-expression specialization and
factory maps are not all implemented in this revision's analyzer. Its reported
benchmark improvements must not be described as current released behavior.
The useful warnings are method-size growth and JVM profile pollution between
benchmark workloads. Keep generated methods bounded and isolate A/B profiles.

## What this does not transfer

SCI primarily uses JVM objects/GC. It does not establish Lean RC equivalence,
unique-constructor mutation, deterministic release, pointer identity, native
Lean layouts, foreign ownership or scalar ABI compatibility.

`src/sci/impl/world.cljc`, `copy-world`/`fork-world`, copies dense cells under a
quiescence gate; registry lineage is shared. `src/sci/fork.cljc` supplies
identity-memoized host policies, rejects recognized affine/unmanaged objects
and shallow-clones arrays. Its default fallback can share unrecognized values.
These are useful explicit boundary policies, not proof of arbitrary recursive
host graph isolation or Ansatz branch-authority semantics.

`src/sci/impl/vars.cljc`, `capture-continuation-context`, captures interpreter
context and persistent dynamic bindings for embedding-provided continuations.
It does not serialize arbitrary active JVM control frames. `doc/interrupt.md`
describes checks at interpreted function/loop entry; host calls can run without
polling. Preserve Ansatz's explicit PC/fuel boundaries and foreign policies.

## Next cheap experiments

1. Measure the prepared interpreter against mutable execution on the same
   bounded corpus, including preparation separately, exact prefixes and fork
   equality. Existing compiled blocks already perform lexical operand fusion;
   mutable gains do not imply gains over compiled RBMap's current measurement.
2. Census RC paths before redesign. `mutable/retain!` rebuilds node maps;
   `release!` allocates a work deque and pair for genuine Ref releases, including
   some nonrecursive/no-op cases. A guarded positive-RC decrement may avoid the
   worklist; preserve task/promise/resource order and COW dirty tracking.
3. Try fixed-arity call/jump adapters independently of the already measured
   direct-call application-map optimization. Preserve simultaneous assignment
   and closure retain/release behavior.
4. Only later test typed Lean IR regions and primitive locals. Nat promotion,
   unsigned wraparound, floats and boxing require Lean-specific contracts;
   SCI's generic Numbers arithmetic does not supply them.
