# Generic represented tail-region implementation plan

Status: M3b preparation and the bounded M3c scalar tail-region executor are
implemented. Broader M3 coverage remains open; see the execution contract and
[validation record](../measurements/typed-tail-execution.json).
The [implementation contract](TYPED_IR_IMPLEMENTATION_SPEC.md) remains authoritative
for execution, snapshots, ownership and admission. This plan makes the remaining
scalar region compiler sequence explicit. It builds on the M2 typed blocks and
M3a wrapper specialization in this repository. Pinned Lean commit:
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

## Recommended first general compiler

Compile arbitrary bounded pure scalar functions with an acyclic intrafunction
CFG into a primitive Clojure `loop`/`case` trampoline for their direct-tail region.
Recognize operations and ABI semantics, never function names or the SUM shape.
The actual imported sum64/sumSize fixtures are acceptance examples, not compiler
patterns. Include mutual tail recursion and unrelated control/data shapes in tests.

First support:

| Construct | First general region |
| --- | --- |
| Parameters/results | uint8/16/32/64 and usize, proven ordinary integer carriers |
| Literal lets | Range-validated typed integer literals, preserve canonical literal carrier |
| Scalar case | M2-supported uint8/16/32, ordered supported alternatives |
| Non-tail direct calls | Exact authenticated pure numeric wrappers only |
| Numeric operations | UInt64/USize add/sub and decEq; extend explicit inventory for more |
| Direct tail calls | Region members, including mutual recursion; optional terminal intrinsic wrapper |
| Return | Scalar operand with complete terminal World materialization |
| Joins/jumps | Initially optimization fallback; M2 validation still supports them |
| Other non-tail calls | Fallback; no recursive guest continuation on JVM stack |
| RC, heap, closures, IO, kernel, foreign values | Fallback, retain existing interpreter/backends |

The no-join restriction is substantive: `mutable/jump-values!` restores captured
locals and body but does NOT trim/restore the joins table. Dead inner join
registrations can remain visible after an outward jump. M2's lexical join context
is not sufficient to reconstruct this dynamic table. Join optimization later needs
runtime declaration-history recipes, complete captured register states and exact
observable dead joins. Do not silently approximate them with current lexical scope.

## Pipeline and APIs

Suggested private/internal compiler boundaries:

    select-tail-region [validated-unit roots descriptors budgets]
    ;; bounded region plus function/entry graphs, or unsupported/budget fallback

    represent-region [selected-region]
    ;; persistent LeanRepresented/1 data, explicit lanes and carrier recipes

    compile-region [represented-region options]
    ;; existing block artifact with execute! and optional execute-budget!

No new public invocation engine. Existing reference/mutable/lazy JVM drivers remain
in control. All preparation is demand-only from the M2 unit and selected roots.
No fresh Init restore. Extern wrappers use the M3a description/validation path,
not fabricated producer companions.

Pattern dialects/passes should validate represented operation forms and make the
logical operation/domain -> storage lane conversion inspectable. A minimal
represented vocabulary includes typed literals, unsigned64 add/sub/eq, case,
logical intrinsic call, direct tail transfer and return. The persistent graph
contains block IDs, not recursively embedded successors. Pattern runs during
preparation/emission, never inside the guest instruction loop.

The represented unit binds M2 schema/profile, demanded source/typed code keys,
actual extern identities/signatures/ownership and built-in semantic generations.
A type such as uint64 is a carrier, not evidence for unsigned operation semantics;
Int64 externs must never accidentally select UInt64 operations.

## Graphs, costs and emission limits

Build the ordinary direct-tail call graph, identify SCCs and include bounded
acyclic tail exits if useful. Non-tail intrinsic wrappers are semantic edges with
an explicit three-instruction trace, not recursive region functions. A first
implementation can compile a bounded tail-closed group of SCCs into one dispatch
without needing a global whole-program analysis.

Within each function, independently verify the executable CFG is acyclic. Reject
unexpected cycles with optimization fallback. Excluding join/jump makes this a
small check; retain explicit graph/cost validation rather than relying only on
producer assumptions. Compute the worst function-entry -> tail/return cost by
DAG dynamic programming: literal1, case1, non-tail intrinsic call3, direct tail1,
return1. Costs include all expanded guest instructions. Tail recursion is NOT
part of this finite bound; it belongs to the outer trampoline loop.

Check structural work, functions, blocks, alternative/argument items, parameter
lanes, expanded emission work and constant pool budgets before generating forms.
Unique-node count alone does not bound emitted code when branches duplicate shared
suffixes. A bounded topological sub-block emitter avoids some duplication; a first
recursive emitter must charge every expanded path before construction.
Do not add one loop argument for every canonical register. Loop carries function
tag and bounded parameter lanes/tags; per-function locals stay lexical inside its
case arm. This avoids huge sparse IDs and every function's locals in every recur.
Suggested initial max-params16 is a compiler budget, not a Lean language limit.

Reuse existing realized-form checks and JVM method-too-large handling. If a whole
function chunk cannot fit safely, fall back for this candidate region; do not
invent arbitrary partial-region reconstruction in this first change.

## Primitive values and canonical carriers

Internal unsigned64/usize values use long bits. UInt8/16/32 fit positive long
lanes initially. Arithmetic wraps; comparisons use the explicit unsigned domain.
Add decEq to the shared M3a ABI/semantic registry, returning logical uint8.

Bits alone are insufficient for exact visible carriers: imported literals keep
their source integer objects, wrapper add/sub results are BigInt even when small,
eq results are Long, and tail arguments preserve the operand's carrier.
Represent each logical value by bits PLUS a carrier recipe/tag. Accept Long and
Clojure BigInt at entry initially; other valid scalar carriers fall back.
Propagate the tag with parameter and tail transfers. A static literal recipe can
refer to its immutable constant; arithmetic result recipe is unsigned BigInt;
eq is Long. Dynamic parameter tags can be tiny primitive integers. There is no
need to allocate boxed values on every tail iteration: materialize at exits only.
No negative bit-pattern Long may escape as a public UInt64 value.

## Logical trace and entry checkpoints

Each represented operation refers to a canonical function/PC. A non-tail numeric
wrapper call carries the trace:

    caller call PC       charge1, save caller continuation/locals/joins
    wrapper runtime PC   charge1, bind wrapper result
    wrapper return PC    charge1, restore caller and bind destination

Its full optimized result is one primitive computation, but its cost is3 and it
updates logical maximum frame depth to at least1. Physical frame allocation may
be elided; the statistic may not. Tail calls clear every old local and joins table
before binding callee parameters (`mutable/call-values!`, around line472).
A producer vdecl+ret folded into legacy :tail costs only the existing one tail
instruction; M1 producer origins do not create an extra runtime step.

For the first implementation, execution commits only complete function chunks.
At a current entry, if remaining fuel is less than that function's worst path,
materialize the entry and return to the existing driver, which executes the
remaining prefix. This avoids arbitrary midchunk deoptimization. Tests must still
cover every fuel prefix: the generic interpreter supplies those short prefixes.

The trace is explicit plan data for cost/proof/auditing and future fine-grained
checkpoints. Initially only two kinds of physical reconstruction are needed:
entry, and actual terminal return. No per-instruction runtime table lookup.

A missing case alternative or any unavailable pure proof must exit at the current
entry before committing that chunk. All calculations inside this subset are
known pure/total, so speculative computations can be discarded and ordinary
interpretation can produce its canonical error prefix. Never apply this replay
strategy to heap/RC/IO or opaque callbacks. Unsupported operations reject the
region during preparation rather than discovering support after effects.

## Executor integration

Existing `block_compile/run!` and `lazy_runtime/run!` pass only Machine to
`:execute!`. They know the remaining fuel. A multi-iteration fast loop needs an
optional artifact hook:

    :execute-budget! (fn [machine remaining-fuel] ...)

Keep `:execute!` as one bounded function chunk for step-region!/step-block! callers.
Both existing run loops choose the budget hook when present and measure actual
steps from the Machine as they already do. The hook never consumes more fuel than
provided. A finite max-chunks-per-entry bound lets it yield, recheck semantic guards
and avoid an arbitrarily long host optimization call. No extra scheduler.

The generated loop holds current function tag, parameter bits/tags, remaining
fuel, accumulated steps and peak-elided-frame indicator. Each complete path
computes its actual trace cost. A tail branch recurs with simultaneous new args
and resets function-local state implicitly (new lexical arm); no old local is
carried unless passed. A return branch materializes its full canonical state.

When the next chunk lacks fuel or a supported guard, flush the accumulated
completed chunks at the next canonical function entry. The normal driver will
pause or interpret the remaining prefix. Do not set :paused prematurely while
there is unconsumed fuel. Guard step-counter overflow conservatively against the
supported counter domain; integer fuel may exceed long range in the old API.

## Materialization ABI

Add narrowly scoped trusted mutable helpers, rather than reaching into control
array indices from emitted code:

    materialize-entry! [machine function parameter-values logical-steps peak]
    materialize-return! [machine function return-pc all-visible-locals result
                         logical-steps peak]

These are internal runtime ABI suggestions, not new admission authority.
The entry helper must use the actual callee register width/layout, clear all
locals/joins, bind only parameters, set actual function entry body, update steps
and max-frames, and leave status running. Existing `call-values!` with a direct
tail application can help perform the clear/bind transition without charging an
extra guest instruction, but constructing it is an exit-only cost and any helper
semantics bypassed by the compiler must be guarded.

The terminal helper reconstructs ALL locals defined on the selected path,
including dead literals/call results, sets the exact return instruction body,
charges all steps including return, retains joins empty in this subset and uses
existing delivery semantics. Entry initially requires no guest frames; therefore
return marks done/result. An optional terminal intrinsic tail must instead produce
that wrapper's final locals/body, not the discarded caller's. Its call/let/ret
trace costs3 and does not itself increase peak frames (it is tail).

Keep heap, globals, next-id, events, entropy/task/stdio state, kernel/source
contexts, allocation count and field-store count unchanged. No guest allocation
occurs in these numeric wrappers, even though the old host runtime allocates
argument vectors, frames and numeric temporaries.

## Entry guards, versions and ownership

Initially enter only actual known function entry PCs with no frames, no joins and
exact parameter-only bound locals. A fuel resume in the middle of a function
uses existing interpretation until a supported entry is reached. Reject native
scalars, unexpected extra locals or invalid carriers by fallback before mutation.

Bind immutable code image/selected function semantics, profile, M3a numeric
registry and definition-owner builtin runtime seals. Tail-region bypasses more
helpers than a wrapper: include call transfer, parameter binding, register width,
frame/return and relevant mutable control helpers in its known-definition seal.
Do not capture current arbitrary redefined roots and declare them builtin.
Reentrant callbacks and effects are outside the region. Supported REPL edits are
observed at region entry/yield boundaries; no claim of atomic behavior under
arbitrary concurrent global with-redefs.

Artifact keys include all demanded typed code and represented operations, transitively
specialized wrapper descriptors, profile/options, compiler generation and semantic
guard generations. Extend lazy matching-hint validation alongside full cache keys:
it historically checked only the five old fields. Samebody/differentregistry shared
cache tests are mandatory. Plans capture immutable code facts/constants, never a
Machine, Source lease, heap owner, active environment authority or mutable World.
Cache ownership/bounds remain program-scoped or explicit shared bounded policy.
Saved parent/sibling Machines remain independent after thaw/freeze.

## Acceptance sequence

1. Pattern represented-pass shape/type/domain tests; source table/origin fidelity;
   exact cost accounting and malformed/unsupported/budget controls.
2. Imported sum64 and sumSize native values55 and wrap2, plus highbit/wrap inputs,
   mutual-tail fixtures, asymmetric parameter IDs/arity, nested branches,
   identity/constant-return, direct tail intrinsic if supported. No name matching.
3. Every fuel prefix of small programs, resume at each prefix and sibling fork:
   compare full World AND explicit carrier classes, return body, all dead locals,
   frames/maxframes, counters and untouched runtime contexts on all backends.
4. Error controls (incomplete case, unsupported/raw input), entering with existing
   frames or extra locals, step counter limits, wrong code/profile/ABI, old/new
   code images, redefs before/after compilation, shared cache/hint invalidation.
   Prove successful tests actually used the region, not only fallback.
5. Paired REPL measurements separate preparation, Pattern lowering, eval compile,
   warm execution CPU/wall/host allocation and logical counters. Compare current
   JVM wrapper tier, mutable/reference and Clojure/Java loops. Small correctness
   gates first; no full Init restart or frontend acceptance for this feature alone.

After this gate, extend lexical joins with full runtime join-history recipes,
then more pure intrinsics and guarded Nat promotion. Heap/RC/interop/kernel regions
need independent failure-prefix and ownership work; keep them interpreted meanwhile.

## Agreed implementation increments and fixed interfaces

M3b first lands preparation data, shared six-operation ABI descriptions and the
one-step equality wrapper, with Pattern shape/lowering, cost, carrier and dependency
tests. It introduces no region executor, mutable materialization helper or driver
hook. M3c then lands emission, materialization and fueled driver integration as
one separately reviewed increment. Neither step is an exact SUM recognizer.

The preparation entry is:

```clojure
(prototype.typed-tail/prepare-region
  runtime-functions selected-typed-functions roots descriptors profile budgets)
;; => {:status :ready :region {:schema "lean-represented-tail/1" ...}}
;; or {:status :fallback :reason keyword :details data}
```

Preparation invokes M2 on demand and consumes its validated blocks. Actual runtime
functions are a separate required input: a descriptor is not proof that an installed
callee remains the ordinary ABI wrapper. Verify demanded wrapper body, parameter
order and actual extern symbol, and selected source implementation semantics.
Retain only bounded, pure demanded dependency facts; never the entire function
catalogue or a World/Source owner. Full M1 typed keys are computed only after bounded
validation; a producer source hash alone is not a typed executable key.

A block ID identifies a lexical validation state. A canonical PC identifies an
interpreter instruction. They remain distinct when a shared suffix has several
blocks. Pattern lowers persistent operation forms once per prepared graph node;
control-flow successor IDs remain opaque IDs. Logical type/ABI validation is separate
from Pattern grammar membership. The represented graph explicitly records long-bit
lanes, literal/Long/unsigned-BigInt/propagated carrier recipes and logical traces.

The shared scalar descriptor keeps `lean-scalar-wrapper/1` vocabulary. Newly minted
descriptions use `unsigned-wrapper/2`, covering UInt64/USize add/sub/decEq. Version 1
remains valid only for the original four arithmetic externs. Equality returns IR
uint8 and a Long carrier; arithmetic retains unsigned BigInt carriers. The one-step
wrapper compiler handles equality with the same guards, fallback and fuel contract.

Pattern is pinned to replikativ/pattern commit
`6d0242ee589d88b336f7dd6f820efa993d2b6f3b` under an optional experiment `:typed-tail`
alias. The core library dependency/AOT path remains unchanged. M3b has a dedicated
bounded CI test lane using that alias; no silent optional test skips. M3c will load
the compiler module only when its option is requested. LLVM is not loaded.

The eventual execution contract is fixed now:

- A running Machine and positive fuel must produce at least one guest step or a
  non-running status. Never flush an entry and return zero steps to redispatch it.
- On a speculative missing-case or invalid proof after prior completed chunks,
  flush the exact next entry, then use the mutable interpreter for all remaining
  fuel. A one-step decline followed by generic JVM execution can reach the older
  generic compiled error-prefix limitation and is insufficient for fueled parity.
- Step-only entry points may decline with one ordinary mutable step; they do not
  claim independently reconstructed multi-instruction error prefixes.
- Full entry guards require actual unambiguous function entry, no live frames or
  joins and exactly parameter locals. Existing unrelated heap, globals, events and
  runtime context are allowed and remain unchanged.
- Historical max-frames survives: materialization uses max(existing peak, elided
  logical peak). Padding for different arities never appears in guest locals.
- Bits and carrier recipes transfer simultaneously across mutual tail calls. All
  visible terminal locals and the exact return PC remain observable.
- Before narrowing possibly BigInt fuel, check finite chunk and signed counter
  headroom. Counter-overflow behavior must be checked against both existing backends before
  M3c claims parity; declining to mutable execution alone is not that proof.

Schema, ABI, carrier, snapshot or authority changes update this plan and the main
implementation contract with their tests. Region execution remains future work
until M3c passes its own complete gate.
