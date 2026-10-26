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

### M2 implemented data contract

```clojure
(prototype.typed-blocks/prepare-unit selected-functions roots profile intrinsics budgets)
;; => {:status :ready :unit unit}
;; or {:status :fallback :reason keyword :details data}

(prototype.typed-blocks/legacy-body prepared-function)
;; => reconstructed canonical interpreter body
```

`selected-functions` must contain paired canonical outputs of
`lower-typed-declaration`, rather than independently assembled bodies and
companions. Minimal M1 facts cannot authenticate literal payloads against a
source digest without the original producer row. M2 validates represented
structural alignment and scope; it does not authenticate source provenance.
A source key is retained as provenance data, never admission authority.

The closed profile shape is:

```clojure
{:schema "lean-block-profile/1"
 :producer-commit "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
 :phase :expanded-rc :word-bits 64 :layout :lean-64
 :abi-generation "ansatz-runtime/1" :target :jvm}
```

The producer digest and ABI generation are explicit caller obligations. The
profile neither verifies upstream checkout identity nor grants execution
capabilities. Unsupported phase/word/layout/target combinations fall back.
Budgets require positive integer `:max-functions`, `:max-instructions`,
`:max-blocks`, `:max-work` and `:max-registers`. Function budget counts demanded
signatures, including extern descriptors. Instruction budget counts unique
canonical instruction identities; block budget counts lexical validation states,
including revisits of shared nodes. Work counts collection entries before
parameter, operand, alternative, root and companion scans, plus visited states
and names. It is a conservative work counter, not an allocation or CPU quota.
Register indices must be below `:max-registers`. Limits stop preparation with a
fallback before any guest execution.

The initial persistent encoding is:

```clojure
{:schema "lean-blocks/1" :profile profile :profile-key profile-key :roots roots
 :intrinsics {demanded-name descriptor}
 :counts resource-counts
 :functions
 {name {:name name :params typed-parameters :result-type ir-type
        :source-key producer-source-key :entry block-id :entry-pc canonical-pc
        :instructions [{:pc canonical-pc :form childless-legacy-form
                        :children [canonical-pc ...]} ...]
        :origins {canonical-pc {:producer-node-ids [producer-id ...]}}
        :blocks [{:id block-id :pc canonical-pc
                  :params {:kind :canonical-registers :types {var-id ir-type}}
                  :scope {var-id ir-type}
                  :ops [typed-operation ...]
                  :terminator typed-terminator} ...]}}}
```

One canonical instruction forms one block initially. Canonical PCs are stable
identity-indexed sites within the selected function, independent of producer
postorder IDs. Multiple lexical states may reference the same PC. The instruction
table retains every canonical operation and reconstructs the original body
stack-safely without tree-expanding a shared DAG. In particular, a folded tail
has one canonical instruction and both producer origins. It still costs one
existing interpreter step.

Register block parameters use a persistent map, shared with `:scope`, rather
than copying all preceding binders into a parameter vector at each instruction.
An ordinary edge has `:args {:kind :identity-registers}`. A call continuation has
`:continuation-args {:kind :call-result :dest id :preserve :identity-registers}`.
Case alternatives retain ordered `[tag {:block id :args identity-transfer}]`
entries. A join descriptor has typed `:params`, declaration-scope `:captures`
and its body `:block`; its continuation carries an identity transfer. A jump
records that descriptor's captures, target block and argument vector with
`:transfer :simultaneous`. All source arguments must be read before writing join
parameters. Captures and scope maps describe types, not saved runtime values.
The canonical table is the reconstruction description; future execution must
still reconstruct actual complete World values.

The supported slice consists of in-range unsigned integer literal lets, direct
calls/tails with demanded signatures, returns, lexical joins/jumps and scalar
cases over UInt8/UInt16/UInt32. Cases require unique tags and at most one default,
placed last. Native Lean selects alternatives in source order whereas the hosted
reference chooses explicit matches before a default; this restriction avoids
that existing disagreement. UInt64/USize case interpretation also needs a later
explicit domain/profile treatment and currently falls back. Heap, RC, runtime,
closure, initialized-global and aggregate operations remain interpreted outside
this preparation slice.

Pinned `Lean/Compiler/IR/Checker.lean` uses one globally fresh index namespace
for variables and joins, including distinct branches. A repeated shared binder
region is invalid under its structural traversal; shared binder-free terminals
are supported. A join body sees outer joins and its own parameters, but not the
newly declared join itself. Its continuation sees the new join. M2 rejects
unknown locals/joins, duplicate binders, arity mistakes and companion/op/ID
mismatches. The pinned checker does not establish exact call/return/jump type
compatibility for all representation-compatible IR. Missing stronger type proof
therefore causes optimization fallback, rather than asserting the Lean source
is malformed.

An intrinsic descriptor has closed fields `:params` (typed/borrowed parameters),
`:result-type`, nonempty `:generation` and nonempty `:extern` symbol string.
Only demanded descriptors are validated and retained. These are call boundaries,
not intrinsic implementations, and no wrapper instruction or fuel is removed.
Extern bodies without typed producer companions are unsupported as unit roots.

M2 has no executable artifact cache or block execution backend. `:profile-key`
is only a profile key: a later artifact key must also cover complete typed code,
compiler generation and exact demanded intrinsic dependencies. The canonical
roundtrip tests execute reconstructed legacy bodies on existing backends; they
do not claim that the new block encoding executes independently. Native value
and ABI conformance and optimized chunk reconstruction remain M3 gates.

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

### M3a implemented selected unsigned wrappers

The first execution increment is opt-in on existing eager/lazy JVM backends:

```clojure
(prototype.runtime-abi/describe-scalar selected-extern-row profile)
;; => immutable descriptor, or nil for an unspecialized supported extern

(prototype.lazy-runtime/open-program functions
  {:scalar-wrappers {name descriptor}})

(prototype.block-compile/compile-program functions nil
  {:scalar-wrappers {name descriptor}})
```

`describe-scalar` shares ordinary `runtime-abi/lower` signature validation.
Default lowering output is unchanged. Descriptors have closed fields:

```clojure
{:schema "lean-scalar-wrapper/1" :name lean-name :extern "lean_uint64_add"
 :params [{:id 1 :type "uint64" :borrow false}
          {:id 2 :type "uint64" :borrow false}]
 :result-type "uint64" :profile block-profile
 :domain :unsigned64 :operation :add :lane :long-bits
 :semantic-generation "unsigned-wrapper/1"}
```

The profile is the M2 profile above, with the pinned producer commit. Only
UInt64/USize add/sub are implemented, and only the 64-bit guest layout. The exact
extern symbol determines the unsigned domain; IR `uint64` alone does not imply
UInt64 rather than Int64. Selected registries contain at most 64 descriptors.
Name spines have a 4096-part limit and parameter indices are at most 65534, leaving
room for the wrapper destination. Descriptors are validated and copied to plain
immutable data, discarding metadata. They grant no source, kernel or execution
admission authority. Every supported public compilation entry validates options;
caller-supplied dependency tokens cannot bypass ABI validation.

Recognition requires the exact standalone wrapper generated by `runtime-abi/lower`,
including the selected function's parameter order and `:runtime-extern` field:

```clojure
[:let destination [:runtime actual-symbol [[:var a] [:var b]]]
 [:return [:var destination]]]
```

The represented descriptor feeds an `eval`-emitted executor with `:max-cost 1`.
It handles only this let. Guest call, wrapper return and all existing frames and
fuel positions remain real. The executor guards before changing guest state;
on failure it calls `mutable/step!` at the current PC. Valid exact Long and BigInt
carriers in 0..2^64-1 become primitive long bit patterns, use wrapping add/sub and
materialize the same positive BigInt result carrier as the reference runtime.
Negative longs, arbitrary Number subclasses, NativeScalar, uncommon integer
carriers, unbound registers and invalid ranges use the interpreter. Failed
operations retain its charged step and exact mutable error state.

Definition-owner baselines cover the bypassed numeric helpers, scalar validation,
native/reference classification and mutable runtime expression path. Checks
compose owner baselines rather than blessing arbitrary foreign functions present
at compilation. Current earlier runtime dispatch memberships must still route the
selected symbol to numeric evaluation; malformed or custom routing table
containers decline without invoking them. Guards also bind machine, native,
scalar, primitive, mutable, emitter and ABI owner generations. Reloading an owner
invalidates old specialization; fallback observes current runtime semantics.
Sequential supported runtime helper/table redefinitions before and after
compilation are covered. Arbitrary Clojure core changes, tampering with private
guard/compiler APIs, concurrent `with-redefs` and atomic redefinition across an
executing instruction are outside this contract.

The lazy key adds a sixth field only for a matching selected wrapper. It binds
the full descriptor/profile and owner generations; shared identity hints check
this extension before reuse. Eager reuse also compares the current per-body
extension, including when equal bodies have changed ABI/parameter metadata.
Default keys retain their existing five-field shape. Executors capture immutable
code, descriptors and generation tokens, never Machine, Source, World or authority
owners. Their internal diagnostic return is `:specialized` or `:interpreted`;
existing dispatch ignores this host-only result.

This is not general represented-block compilation. M2 blocks are not yet consumed
by a representation pass, Pattern remains optional and no LLVM is needed. Full
scalar regions, tail-call SCC compilation, guard amortization and reconstruction
of inlined call/wrapper/return traces remain subsequent M3 work. The existing
generic compiled path's broader failure-prefix limitation is unchanged: the exact
error-state guarantee here applies to recognized standalone wrappers and their
guarded interpreter fallback.

Focused [validation and paired measurements](../measurements/scalar-wrapper-specialization.json)
use actual pinned exported extern declarations, actual exported Lean UInt64/USize
sum programs, a pinned native header oracle and native Lean program results.
The reusable [benchmark](scalar-wrapper-benchmark.clj) runs inside the existing
REPL. It separates fresh plan compilation with already loaded compiler classes
from warmed execution, includes thaw/run/freeze for mutable/JVM paths and checks
complete Worlds outside timing. These small experiments do not establish steady
host-JIT performance, whole-library coverage or hosted frontend acceptance.

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
M2 provides bounded scalar control-flow preparation and exact canonical body
reconstruction, with focused [validation results](../measurements/typed-block-preparation.json).
M3a adds guarded UInt64/USize wrapper-let specialization on existing JVM backends.
General represented-block execution, kernel/interop integration and remaining
milestones are still implementation work.
