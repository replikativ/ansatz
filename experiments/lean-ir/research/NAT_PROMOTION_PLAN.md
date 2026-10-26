# Guarded Nat specialization and promotion plan

Status: source audit / proposal only. No JVM startup, new execution evidence or
implementation edits. Current M3c handles UInt64/USize; Nat is not implemented.
Reference worktree: `.tmp/ansatz-typed-tail-execution`.
Lean commit: `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

## Recommendation

Extend the SAME M2 -> Pattern represented operations -> typed-tail emitter ->
existing lazy JVM driver with guarded small host-Nat values. Start with ordinary
Long inputs in 0..Long/MAX_VALUE and the externs Nat.add, Nat.sub and Nat.decEq.
Add Nat.mul later behind its own nonoverflow guard. Admit inc/dec as exact
one-step no-ops only for proven nonreference numeric values. Preserve the current
whole-function-chunk checkpoint strategy.

When an operation would leave that small range, abandon the uncommitted current
chunk, materialize its canonical entry and let the existing interpreter execute
the remaining fuel, including promotion to host arbitrary precision. Do not emit
a wrapping Long, an invented guest MPZ object or a new invocation engine.

Describe this first result as **small-Nat compilation with promotion fallback**.
It is not compiled big-Nat arithmetic, native MPZ allocation fidelity or complete
Nat/Int support. Those are separate follow-up gates.

## Carrier audit

| Carrier | Existing hosted meaning / behavior |
| --- | --- |
| Ordinary Long / Clojure BigInt | Exact semantic integer; Nat requires nonnegative, Int permits negatives. Also accepted integer classes by generic integer? boundaries; optimized subset may conservatively accept fewer. |
| RawNativeScalar | Untyped native immediate payload, 0..2^63-1. Nat interprets payload directly. Int interprets low unsigned32 then signed32, NOT signed63. |
| Ref to :mpz node | `native/number-value` borrows `:integer` after validating kind, empty fields and integer payload. Nat additionally rejects negative payload. |
| Imported :mpz Ref | ModuleData creates tag250, rc0 persistent nodes. Native imported ranges are immutable. Retain/release does not decrement them. |
| Local owned :mpz Ref | Generic heap API/checkpoint can represent one, but current numeric runtime does not normally CREATE these. Explicit RC instructions own its lifetime. |

Sources: `native_scalar.cljc:5-58`, `module_data.clj:68-115`,
`machine.cljc:20-45,64-72,93-122`, `mutable.clj:296-333`.
`interop_codec.clj:100` encodes Nat as `[world host-integer]` without guest heap
allocation; `:nat` decoding at line127 borrows through native/nat-value. It does
not turn a host BigInt into a guest MPZ Ref. There is no general :int codec in
that initial descriptor inventory.

Production source search found :mpz node creation in `module_data.clj:115`,
including its callers for imported/native stores. No numeric arithmetic producer
allocating new local :mpz results was found. Tests or callers can construct local
owned MPZ nodes via generic allocate/replace/checkpoint machinery; they remain
important RC test inputs even if uncommon in the frontend path.

## Native thresholds and semantics

Pinned `lean.h:1475` defines `LEAN_MAX_SMALL_NAT = SIZE_MAX>>1`, hence2^63-1 in
the admitted64-bit profile. Nat add uses unsigned size_t and promotes above that
threshold; sub saturates at zero; mul checks product overflow and promotes.
Inputs are borrowed (`b_lean_obj_arg`). Source: `lean.h:1495-1551`.

Native small Int is different: `LEAN_MIN_SMALL_INT/LEAN_MAX_SMALL_INT` are
INT_MIN/INT_MAX on64-bit, and scalar decoding casts unsigned32 to signed32.
Source: `lean.h:1687-1735`. Do not infer Int limits from Nat or UInt64 lanes.
Native negative Int encoded as RawNativeScalar must retain its contextual signed32
interpretation. `lean_nat_abs` is the Int absolute-value operation despite its
symbol prefix; it must not select Nat-input proofs merely by prefix.

Numeric IR literals in object/tagged/tobject are native Nat literals, as shown
by `src/library/ir_interpreter.cpp:580-610`; the hosted importer preserves a
numeric literal's actual host integer carrier. IR object types alone still say
nothing about arbitrary parameter values or whether they denote Nat.

## Ownership: verified, not a hypothetical Nat.add leak

The actual inventory has **borrow true for both parameters** of lean_nat_add,
lean_nat_sub and lean_nat_mul (`runtime_signatures.edn:644-647,686-689,702-705`).
This matches native b_lean_obj_arg. Therefore arithmetic not releasing an input
MPZ Ref is correct. A surrounding function can own its parameters while calling
a borrowing extern; the producer then emits separate dec instructions.

Nat.toInt is owned (`runtime_signatures.edn:706-707`). Native lean_nat_to_int
transfers an existing MPZ object unchanged; hosted runtime_prim/evaluate explicitly
does the same, without an unnecessary release/reallocation (`:358-365`).
The `_of_nat_mk` conversion path releases an owned MPZ input once after computing
its unboxed result (`runtime_prim.cljc:366-371`), matching native constructors.
Do not report an owned Nat.add MPZ leak: source audit does not support that claim.

Aliased input refs count as separate borrowing uses but incur no implicit retains
or releases in these externs. Caller inc/dec occurrences remain explicit and
must not be merged away without their existing ownership proof.

## Real hosted/native representation and allocation difference

`runtime_prim.cljc:228-271` computes exact Nat/Int arithmetic using Clojure +',
*', negation and arbitrary precision. `evaluate` returns `[world result]` for
these operations, with no allocation of a guest :mpz node. Arithmetic on borrowed
imported MPZ values likewise returns an ordinary semantic host integer, not a
new Ref. Therefore crossing2^63-1 changes a Long to host BigInt, but normally
does NOT change hosted heap, next-id, RC or logical allocation statistics.

Native Lean allocates an MPZ result when required:
`src/runtime/object.cpp:1362-1460` uses alloc_mpz/mpz_to_nat_core;
alloc_mpz calls lean_alloc_small_object, whose `lean.h:482-484` calls
lean_inc_heartbeat. Native arbitrary precision allocation is thus guest runtime
allocation work; it is not equivalent to an uncharged JVM BigInt box.

Hosted `runtime_heartbeat.cljc:1-5` explicitly defines its current profile as
logical guest heap allocations, excluding JVM allocations, native allocator
block sizes and Java kernel work. Its allocation-count derives the modeled heap
counter. Current hosted big-number arithmetic does not charge an MPZ allocation.
This is an existing profile difference, not a new compiler optimization freedom.

The compiler must preserve the hosted reference World for this declared profile,
while native value/ABI comparison remains an independent oracle. Document that
native MPZ identity/allocation/heartbeat parity is NOT provided. If native-style
number allocation/identity becomes required, implement it systematically in the
reference runtime and all backends first, version the runtime profile and define
fresh acceptance evidence. Do not secretly add MPZ IDs in this compiler alone.

## Required preparation extensions

Current M2 initially accepts only numeric scalar literals and uses exact IR type
compatibility; Nat programs typically use tagged literals as arguments to tobject
externs. Actual `fixtures/globals.jsonl` GlobalProbe.seed uses tagged1 followed
by Nat.add. Normal Nat loops also emit inc/dec; actual
`fixtures/module-import-bulk.jsonl` List.range.loop and Nat.toDigitsCore contain
explicit dec on Nat arguments/results.

Extend M2 to retain object-family numeric literal facts and inc/dec facts, with
closed shapes, borrowing/persistent/count annotations, exact canonical fuel,
origin and roundtrip. Make safe object/tagged/tobject ABI compatibility explicit;
do not assert a stronger equality that Lean's producer does not require. Stronger
optimization proofs remain a separate represented-stage decision.

Represented values add a refinement such as:

    {:ir-type "tobject" :domain :nat-integer :lane :nonnegative-long
     :proof {:kind :entry-guard | :nat-extern-result | :numeric-literal}}

Keep IR type, semantic Nat domain, physical lane and ownership separate. Obtain
semantic operation from the exact validated extern descriptor, not just object
type or function label. Entry guards prove the actual values are ordinary
nonnegative Longs. Unsupported object values (Refs, constructors, foreign objects,
RawNativeScalar, BigInt) initially fall back before changing the Machine.
Unused/general object parameters are not silently deemed Nat by their IR type.
The region only admits operations whose required domain proofs are established.

Extend the existing shared registry/definition-owner semantic seals with Nat
operations. Signed/fixed-width operation symbols do not match Nat descriptors.
Every bypassed nat!/number-value/exact!/add/negate validation function and operation
mapping is a guarded dependency, including mutable reference classification.
Keep keys/profile, compiler generation, descriptors and lazy shared-hint matching
in sync with the existing M3 machinery.

## Fast operation semantics and RC

With both inputs ordinary nonnegative Long and at most Long/MAX_VALUE:

- Add: allow only `a <= Long/MAX_VALUE-b`; otherwise request promotion exit.
  The successful result is a nonnegative Long, matching generic +'.
- Sub: if a<b return Long0, otherwise a-b. It saturates; never use UInt64 wrap.
- Eq: Long0/1, logical result uint8; no promotion needed.
- Later mul: zero is allowed; otherwise `b <= Long/MAX_VALUE/a` before multiply.

Use existing literal recipes to preserve parsed literal carriers. Initially use
Long-only entry/results for this lane. Accepting small BigInt inputs needs
separate carrier propagation because +'/sub may preserve BigInt even when the
numeric result fits Long; do not normalize them silently. NativeScalar support
also needs its own exact original-carrier recipe, not just payload bits.

Inc/dec of a proven nonreference Nat value is a logical one-step no-op, including
its check/persistent semantics under the guarded reference classifier. It does
not unbind the local; dead-but-visible values remain in snapshots. If the operand
could be a Ref, the region is unsupported. Never erase MPZ RC merely because the
numeric payload fits a primitive lane.

## Promotion exit and failure prefix

Reuse current whole-function chunk bailout. When a checked add/mul would exceed
the range, do NOT charge any part of the current uncommitted chunk and do NOT
materialize its speculative local values. Reconstruct the current function ENTRY
using the entry parameter values/carrier recipes; flush only earlier completed
chunks and their max-frame statistics. Delegate remaining fuel to u/run! using
the existing fallback path. Its positive fuel guarantees forward progress.

This can replay pure comparisons, arithmetic and nonreference RC no-ops from the
uncommitted chunk; it cannot replay heap mutation, external effects or opaque
callbacks. No such operations are admitted. The reference interpreter then
performs the exact call/wrapper/return/RC instruction prefix allowed by the fuel,
including Long->BigInt promotion. Current runtime increments instruction steps
before an operation, so errors must still follow that interpreter path.

A first implementation may remain entirely interpreted for the rest of the run.
If a subsequent public call reaches another region entry containing BigInt,
its Long-only guard rejects it. This is correct promotion fallback, not compiled
promotion or automatic big/small respecialization. Shrinking BigInt back into
range does not justify changing its carrier class.

## Suggested reviewable PR and gates

One PR can extend the existing typed blocks/registry/Pattern/emitter with the
three Nat operations and nonreference RC no-ops, plus explicit promotion exit.
It must not introduce a second interpreter, name-based SUM recognizer or MPZ
allocator. Split M2 facts/roundtrip from execution if review size becomes large.
Keep Int support and native-style MPZ allocation policy outside this PR.

Acceptance:

1. Small actual Lean Nat tail-recursive program(s), plus identity/constant-return,
   saturation subtraction, asymmetric/mutual-tail examples and real inc/dec sites.
   Confirm the emitted IR rather than assuming source-level Nat maps like UInt64.
2. All small fuel prefixes, resume and saved siblings, full World AND carrier-class
   checks. Include dead locals after RC, maxframes, next-id, heap, allocations,
   heartbeat contexts and untouched source/kernel state.
3. Boundaries MAX-1,MAX,MAX+1; add crossing after several compiled iterations and
   overflow late in a chunk; sub a<b; mul overflow when added. Assert optimized
   chunks occurred before promotion, exact entry bailout occurred, and native
   mathematical values match independently.
4. BigInt/RawNativeScalar/MPZ Ref entry rejects fast path without guest mutation.
   Invalid negative Nat inputs get the reference error and step prefix. Inspect
   full error data/state, not only result value.
5. Borrow/ownership controls using BOTH imported rc0 and local rc1/rc2 MPZ refs:
   Nat.add/sub/mul borrow without RC changes; caller inc/dec control lifetime;
   Nat.toInt transfers owned ref; _of_nat_mk releases once; aliased borrowed refs
   do not acquire imaginary ownership. These controls run interpreted initially.
6. Redefs before/after compile, code/profile edits and shared-cache hints, root
   retention and bounded budgets. Fresh semantic generation/key changes.
7. Separate REPL preparation/Pattern/eval compile time, hot CPU and host allocation
   measurements. Report promotion fallback separately from successful fast paths.
   No repeated Init/bootstrap or large heap is needed.

## Small REPL audit proposal (later, not executed here)

Use one existing small REPL; require runtime-prim/machine/native-scalar only.
Create world W with a local MPZ node via m/allocate :mpz250[], then replace its
node with :integer=2^63 or a negative Int and rc1. Build the ordinary existing
injected heap ops table (or execute exact ABI-lowered wrappers) rather than a
new test-only runtime. Run Nat.add of borrowed Ref+Long1, inspect input rc and
result carrier plus allocation/next-id deltas. Expected current behavior: input
rc unchanged, host BigInt result, zero extra guest MPZ allocation.

Then run caller dec and verify local node disappears; repeat rc2, aliased refs,
imported rc0 and retained sibling W. Test Nat.toInt returns the same MPZ Ref,
and owned UInt64.ofNat_mk releases the local input once. Compare value oracles
against pinned native Lean, while explicitly expecting its MPZ allocation policy
to differ from current hosted logical-allocation profile. This diagnoses actual
ownership bugs without inferring one from a borrowing arithmetic call.

Pinned native sources:
- https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/include/lean/lean.h#L1475
- https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp#L1362
- https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/ir_interpreter.cpp#L580
