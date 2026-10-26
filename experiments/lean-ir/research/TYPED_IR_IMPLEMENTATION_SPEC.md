# Typed Lean runtime implementation contract

This contract fixes the implementation sequence and compatibility boundaries for
typed Lean execution on Ansatz. The
[compiler design](TYPED_IR_PATTERN_DESIGN.md) explains the architecture and Pattern
languages. This file defines the interfaces and acceptance gates used to implement
it. Future compiler interfaces below are internal contracts, not shipped public
APIs.

## Required behavior

The existing reference interpreter defines hosted instruction fuel, complete
World snapshots and modeled ownership behavior. Native Lean supplies the
independent value, layout and ABI oracle. Optimized execution must satisfy both
within the declared producer/runtime profile.

The implementation preserves:

- Existing untyped declaration loading and per-declaration representation; no
  default eager companions. Loading the new namespace adds fixed initialization.
- Exact paused/completed World state, including dead-but-visible locals,
  continuations, IDs, ordered events and runtime context.
- Saved parent and sibling isolation, including Source lifetimes.
- Lean logical ownership, errors, resource effects and hosted heartbeat charges.
- Old code/environment versions after REPL edits.
- Kernel checking and admission authority independently of execution.

Unsupported optimizations fall back before guest work. Invalid typed facts,
source mismatches and incompatible ABI declarations are validation errors.
Optimization does not turn invalid input into an admitted program.

## M1 demand driven typed companions

Ordinary `prototype.import-ir/lower-declaration` and `load-bundle` keep their
existing output and behavior. Typed preparation is explicit:

```clojure
(prototype.typed-ir/companion producer-fdecl)
;; => immutable companion

(prototype.import-ir/lower-typed-declaration producer-row)
;; => [name (assoc legacy-function :typed-ir companion)]

(prototype.typed-ir/typed-code-key typed-function profile)
;; => semantic cache key
```

The compiler obtains one selected declaration from the existing authenticated
catalogue or source provider. It does not eagerly prepare every declaration,
restore Init or retain the fetched row. These operations issue no execution,
publication or kernel-admission authority.

The companion has this closed top-level vocabulary:

```clojure
{:schema "lean-typed-companion/1"
 :node-space :producer-ir
 :source-key source-merkle-key
 :signature {:params [{:id 0 :type "uint64" :borrow false}]
             :result-type "uint64"}
 :root node-id
 :nodes [typed-site-facts ...]}
```

Nodes are compact maps with an `:op` and child IDs. Binding facts retain variable
ID and result type; join facts retain join ID and typed/borrowed parameters; case
facts retain scrutinee ID, IR type, type name and ordered alternative descriptors;
RC facts retain count, conditional-check and persistent flags. Other body forms
retain their source kind and edges. The executable body retains operation data.

IDs describe producer body sites, not normalized interpreter PCs. In particular,
lowering a full application followed by return can produce one legacy tail
instruction from two producer nodes. M1 must not claim a one-to-one origin map.

Traversal is stack-safe and visits shared body nodes once by identity. Shared
children remain shared by ID. No raw declaration, Source, World, native pointer
or capability owner is retained in a companion.

M1 admits nonnegative producer IDs and indices through Integer/MAX_VALUE;
execution register limits and compilation budgets are checked separately.

Source identity is computed with a per-preparation DAG memo. Hash each node's
source payload and child keys, then the declaration header and root key. Do not
feed a complete shared source graph to a tree-expanding hasher, or retain its
root in the existing strong fingerprint cache.

M1 validates types, parameter shapes, borrow flags, natural IDs and structural
body facts. It rejects duplicate IDs within parameter lists. Scoped use-def,
dominance and complete call typing belong to M2; companions alone are not typing
proofs. A global variable-to-type map must not erase lexical site distinctions.

The typed key includes schema, complete companion, executable function semantics
and explicit producer/runtime profile. Relevant type, borrow, result, case, join,
source or profile changes invalidate it. Clojure metadata is not an identity
channel. Existing untyped compiler keys retain their existing contract.
The M1 profile is immutable plain data with symbolic versions or digests; a JVM
compiler-instance identity guard belongs to the enclosing artifact cache.

Companion data must not look like executable operand/instruction vectors to the
legacy slot counter. Register width must remain identical for legacy and selected
typed functions. Memory is bounded by explicitly selected compilation units.

## M2 validated control flow

`prepare-unit` takes selected typed functions, a validated profile, an immutable
intrinsic registry and explicit budgets. It returns either a validated plan
description or a fallback reason. It performs no guest execution and publishes
no new environment or World.

The profile binds producer commit, admitted compiler phase, guest word size and
layout, runtime ABI/intrinsic generation and target. A caller-supplied map is
not evidence that the enclosing source/capability checks succeeded.

The `LeanBlocks` encoding uses persistent function maps containing a name,
typed parameters, result type, entry block and block table. A block contains typed
parameters, ordered operations and one terminator. Operations and terminators
carry stable instruction positions. Block references are IDs, not recursive
copies of successor blocks.

Validation checks lexical resolution, dominance, fresh definitions, block/call
arity and type compatibility. Join context becomes explicit block arguments
where necessary. Argument transfers evaluate all sources before overwriting any
destination. Erased and void slots retain canonical ABI identity.

Unit preparation is demand-driven from roots. Function/node/region budgets stop
optimization with a fallback reason. No pass scans all Init definitions merely
to compile a small requested unit. Prepared plans are owned by a program or kept
in bounded caches.

## M3 represented operations and JVM execution

Logical IR types and operation domains remain distinct from storage lanes.
The initial lanes are references/boxed carriers, long integer bit patterns,
int bit patterns, double and float. Unknown values retain their generic carrier.

The intrinsic registry extends the existing raw ABI inventory. Each entry binds
its actual extern identity and signature, semantic operation, operand/result
types and domain, borrowing/ownership, effects, failure behavior, interpreter
implementation, specialization guards and code dependencies.

Start by specializing runtime expressions inside their existing extern wrapper.
Do not initially remove the guest call and return: their fuel, frame depth and
intermediate state remain real. Later inlining requires a logical trace and
reconstruction recipe for those removed operations.

`compile-region` consumes validated represented blocks and emits Clojure forms
through `eval`. Pattern dialects and passes perform preparation; they do not
execute in the guest instruction loop. Compilation time is measured separately.
JVM method-size budgets split regions or retain interpreted boundaries.

`run!` accepts a plan, a trusted mutable Machine and fuel. The plan captures no
Machine, locals array, heap, environment authority or Source. Entry guards bind
code image, representations and runtime dependencies. A failed specialization
guard delegates to ordinary interpretation before changing guest state.

Complete chunks can remain in primitive locals. Insufficient fuel exits before
the next chunk, reconstructs its exact canonical state and uses the interpreter
for the remaining prefix. Native JVM stack frames cannot become the sole
representation of an arbitrarily resumable guest continuation.

An operation that can fail after effects must identify the correct committed
prefix and owned temporaries. It cannot restart mutated work. Host allocation
elimination preserves logical IDs, counters and release behavior where observed.

## M4 kernel integration

Continue to use the existing kernel bridge and protected environment association
mechanisms. Compilation and typed preparation cannot create checking receipts,
associate an unchecked environment, or authorize imported code execution.

The checking projector and a lossless runtime representation have different
contracts. The current Java kernel projection can erase metadata and normalize
kernel-irrelevant details. Do not replace arbitrary guest Lean.Expr values with
that projection: Lean metaprograms may inspect details that kernel checking omits.
Projection borrows guest values and shares work only within its declared scope.

Kernel operations receive the appropriate environment/version through the
existing runtime context. Plans may cache immutable code facts but cannot bake
in mutable checking authority. Environment assumptions become guarded
dependencies where specialization relies on them.

Checked source declarations and compiler correctness remain separate obligations.
A computed runtime value is not a proof. To publish a theorem, construct and
check the corresponding declaration through the existing kernel admission path.

## M5 Clojure and Java interop

Extend the existing `prototype.interop`, `raw-interop`, `interop-codec`,
`typed-extern` and typed EIO contracts; do not introduce a parallel invocation
engine. Existing public shapes remain compatible while optimization is added.

A callable handle binds a session/code image, selected declaration, explicit
runtime signature and value codecs. Its initial World/environment version is
fixed or supplied explicitly by a validated invocation context. It must not
silently resolve a newer declaration after an edit.

An invocation returns the completed or suspended state using the existing
driver's ownership contract. Decoding borrows guest results; the returned state
owns allocated results until explicit release/disposal. Boundary validation
checks arity, codec, scalar range, World membership and environment association.
IR `object` alone does not infer a Nat, IO action or dependent source type.

Existing scalar, Nat, String, bytes, Bool, Unit, Option and selected IO codecs
remain the initial coverage. New signed-integer and general aggregate codecs
require explicit descriptors and tests. UInt64 host values remain exact unsigned
values; long bits are an internal representation. Floating-point transport keeps
its current bit-preservation contract.

Reverse calls validate the actual extern ABI and declared ownership. Encode a
successful host result before discharging owned inputs, count aliased ownership
occurrences and preserve existing checkpoint/failure packets. Never implicitly
retry effects, roll back an external operation, or finally-drop an uncertain
owner. Typed IO/EIO conversion occurs only through its declared protocol.

Reentrant calls restore the correct scoped session/World. Foreign JVM objects
and closures are capability-backed values unless a codec explicitly defines
persistence. Guest IDs are not native Lean pointers and are not cross-World
handles.

Java bindings are thin adapters over these same invocation/codecs and failures.
They add no second scheduler, heap or ownership policy. Optional native Lean
bindings need their own handle/marshalling and RC lifetime contract; they are not
required for this JVM compiler.

## M6 REPL versions and ownership

Loading A and then edited B creates distinct code/environment images. A retained
A handle and World continue to execute A. B uses B; unchanged compatible artifacts
may be reused by semantic key. Dependent Lean elaboration is still required when
the source dependency changes.

Dynamic host bindings remain live or have guards and invalidation at a supported
execution boundary. Artifact keys include typed code, compiler generation,
target/options and every inlined or specialized semantic dependency.
Invalidation never rewrites an old persistent image.

Lean logical RC, branch storage ownership and JVM GC remain separate. Mutating
shared snapshot storage requires a private copy even when guest RC=1. Imported
RC0 nodes remain immutable. Snapshotting foreign capabilities does not duplicate
external resources or rewind IO. Cycle collection for a guest heap retained by
explicit roots is a separate runtime policy.

## Acceptance matrix

| Milestone | Required evidence before advancing |
| --- | --- |
| M1 | Old import output/meta and behavior unchanged; faithful typed facts on actual fixtures; malformed facts rejected; deep/shared DAG traversal bounded; raw source absent from long-lived caches; typed-key invalidation; unchanged register width |
| M2 | Valid block typing, scope and transfers; malformed joins/calls rejected; every small fuel prefix and saved sibling matches reference |
| M3 | Actual imported UInt64/USize programs, then Nat promotion; native value/ABI oracle plus full hosted-state oracle; compile/run/allocation measured separately |
| M4 | Actual guest kernel operations; protected environment/admission checks, projection ownership and retained old versions |
| M5 | Calls and callbacks on interpreter and JVM tiers; boundaries, aliased owners, typed errors, reentrancy and Java consumer |
| M6 | Edit A to B in one REPL, retain both, reuse unaffected plans, invalidate changed dependencies and preserve siblings |
| Integrated release | Hosted Lean file loading/calls and selected frontend work on the accepted source/class cohort; packaging and documented capability profile |

Small fixtures and the existing REPL are the inner development loop. No repeated
full Init restore or verification is required for an isolated change. Broader
tests and genuine hosted acceptance run at integration boundaries.

Historical source/class cohorts and receipts remain historical. Changing a
runtime source file can invalidate their exact attestation even when behavior is
compatible. Never refresh their hashes to bless a new compiler; produce a
separately accepted cohort before claiming hosted frontend acceptance.

## Change control and implementation status

The implementation follows these gates in order. A deliberate change to schema,
snapshot observability, ownership, kernel authority or interop semantics updates
this contract and its acceptance tests in the same change. Performance-only
rewrites preserve those contracts.

The existing SUM and UInt64 Pattern fragments are research evidence, not general
compiler implementation. M1 provides the demand-only companion and typed-key
APIs, with focused [validation results](../measurements/typed-ir-companion.json).
Scoped typechecking, block formation and subsequent milestones remain
implementation work.
