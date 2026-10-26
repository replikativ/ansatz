# Guarded Nat represented regions and promotion exits

Status: registry/data selection, Pattern forms and versioned proof units are
implemented, with explicit runtime decline before factory creation. Guards,
compiled Nat execution and promotion exits below remain the next increment.
Actual pinned native fixtures are available as independent producer/value evidence. Build
on the existing `prepare-region -> Pattern representation -> primitive trampoline
-> existing eager/lazy drivers` path. Do not add an interpreter or MPZ allocator.

## API and schema

Keep the six-argument `prepare-region` API and current closed `:typed-tail`
configuration keys. No `:entry-domains` option is required: this is a guarded
runtime value specialization, not a claim that an IR object annotation proves
its Lean logical type. General `tobject`/`tagged` parameters may enter the variant
only after explicit ordinary-Long/nonnegative/range checks. Other inputs execute
the original program. Definite-reference `object` parameters remain unsupported
in the first Nat variant.

Introduce `lean-represented-tail/2` and preparation generation `typed-tail/2`
for Nat proof units; legacy unsigned-only units remain `/1` during this additive
data-first transition. Both use the same pipeline, not separate engines. Existing
execution explicitly declines `/2` before factory creation until its emitter
lands. Eventual uniform `/2` output can follow once that consumer is implemented. Existing M2 schema stays `lean-blocks/1`. Existing scalar operation
forms remain structurally compatible; new Nat forms make their domain and lane
explicit. Compiler/context/emitter generation keys invalidate old executable
artifacts; historical `/1` receipts remain historical. Public editable prepared
maps are not executable typing or authority certificates.

Preserve each function's original `:params` entries (`:id/:type/:borrow`). Add one
flat per-function `:representations` table keyed by local ID, shared by that
function's blocks. IDs are fresh only within a function; tables are never merged
across mutual callees without a function key. Example entries:

    {1 {:ir-type "tobject" :domain :nat-integer :lane :nonnegative-long
        :proof {:kind :entry-guard :carrier :long :range [0 9223372036854775807]}}
     2 {:ir-type "tagged" :domain :nat-integer :lane :nonnegative-long
        :proof {:kind :literal :carrier :long :value 1}}}

Every parameter, including an unused one, must have a supported representation
to enter the trampoline. An unused general object parameter receives no static
Nat proof. A successful
entry guard establishes the stated host value refinement for that invocation;
that is the only proof available even for identity/constant functions. Native
pointer typing and Lean kernel admission remain independent. `object` facts do
not become immediate lanes merely because a literal annotation was preserved.

The one-table layout avoids repeated prefix-scope traversal. Derive it from
parameters and admitted literal/intrinsic definitions; debug scopes are not typing
inputs. Tail edges must prove their simultaneous arguments satisfy the target's
representations before guard amortization is allowed.

Extend represented operations rather than inventing a Nat execution engine:

    [:intrinsic origin dest [:repr "tobject" :nonnegative-long]
     :nat :add callee operands [:carrier :long]]

    [:rc origin :inc local count check persistent
     [:repr "tobject" :nonnegative-long] [:proof :nonreference]]

Equality uses the existing uint8/long result representation while retaining Nat
as the operand operation domain. RC retains its complete canonical annotation,
local and one-instruction trace. It is eliminated physically only after a real
nonreference value proof; it still counts one guest step and leaves the local
visible. No MPZ Ref retain/release is eliminated.

## Shared descriptor registry

Extend the existing exact-symbol semantic registry coherently to nine operations:
UInt64/USize add/sub/decEq and Nat add/sub/decEq. Do not recognize Nat by a name
prefix (e.g. `lean_nat_abs` is not a Nat-input operation).

Nat descriptors use the existing closed descriptor shape with `:domain :nat`,
`:lane :nonnegative-long`, `:semantic-generation "nat-wrapper/1"`, canonical
Nat arithmetic result carrier `:long` within this guarded lane, and uint8 Long
for equality. Both Nat inputs are actual borrowed `tobject` parameters, as checked
against the pinned ABI inventory and installed wrapper. Their exact symbol,
IR types and borrowing stay in every demanded descriptor/code dependency.
Unsigned descriptor generations `/1` and `/2` continue to validate unchanged.

The standalone unsigned wrapper compiler must explicitly decline Nat descriptors
until it implements the same checked lane, rather than accidentally applying
64-bit wrapping. Region selection and wrapper validation share the inventory.
Descriptions carry no callable implementation or checking authority.

## Guards and semantic dependencies

Nat entries initially accept exact ordinary Long in `0..Long/MAX_VALUE`.
BigInt, BigInteger, RawNativeScalar, Ref, constructor and foreign values decline
before effects. Nat literals likewise require exact Long plus range proof;
preserved large/tagged or alternate-carrier facts do not silently normalize.
Unsigned full-bit carriers retain their existing behavior and recipes.

Validate Nat literal carrier/range immediately after bounded M2 preparation and
before pure-code hashing or `typed-code-key` can decimalize a large integer.
A class test rejects non-Long literals without creating a new BigInt or decimal
string. Apply an early conservative numeric bound to RC count facts too before
hashing/emission; declining optimization is preferable to unbounded constant work.
Unrequested source/catalogue entries are not scanned.

`interop-codec/encode-value` currently returns `nat!`'s original integer value,
and `nat!` validates then returns its argument unchanged. Thus Clojure Long7 can
enter the first lane, while even small Java BigInteger/Clojure BigInt inputs
retain those carriers and decline. Do not silently normalize codec classes in
this compiler change. Supporting them needs later carrier recipes/partial
specialization or an explicitly versioned common codec profile.

Extend definition-owner semantic seals for each newly bypassed path:
`runtime-prim/nat!`, `numeric`, exact/add/negate and operation dispatch;
`native-scalar/number-value` and its own relevant classifier baseline;
mutable `retain!`/`release!` and `assert-persistent!` plus the definition-owner
`m/ref?` baseline. The current mutable RC functions perform persistent assertions
BEFORE their reference branch, even for ordinary Long inputs; no RC count cast
occurs before the reference branch. The existing M1 typed-companion boundary
already limits RC count facts to `0..Integer/MAX_VALUE`; retain that supported
count profile rather than constructing impossible oversized companion fixtures. Preserve/guard those exact facts rather than
assuming the instruction immediately tests refness. Existing routing,
Machine classification, layout, materialization, caller-depth, compiler and ABI
seals continue to apply. Capture foreign baselines at their definition owners,
never while compiling under a current redefinition. Keep unreachable ref-node
helpers outside the supported path rather than claiming blanket Var coverage.

Any selected descriptor, representation/proof table, source/wrapper code,
compiler/options/profile or semantic dependency change belongs in the region
key, artifact extension and lazy shared-hint checks. The program still prepares
once; entries guard before effects and before forcing the shared factory.

## Arithmetic and materialization

With proven nonnegative Long inputs, add checks `a <= MAX-b` before computing.
Sub returns Long zero when `a<b`, otherwise `a-b`; equality returns Long0/1.
Multiplication, signed Int and compiled arbitrary precision are out of scope.
Successful Nat values use the existing Long carrier recipe0. Do not normalize
small BigInt inputs or allocate guest MPZ nodes.

When add would leave the small range, abandon the entire uncommitted current
function chunk. Preserve the current chunk's original entry values/recipes,
flush only previously completed chunks and their logical maximum-frame peak,
and run mutable interpretation for all remaining fuel. This is the existing
progress-safe bailout path, including saved caller frames and joins. It is not a
one-step decline followed by generic compilation, and never returns zero-step
Running to the driver.

There are no effects in an admitted chunk: only checked arithmetic, cases,
literals and proven nonreference RC no-ops. Replaying an uncommitted chunk is
therefore safe. The interpreter performs actual promotion and full charged error
prefixes. Later public entries with BigInt still decline; this first increment
is small-Nat compilation with promotion fallback, not compiled big-Nat support.
The hosted semantic-integer/logical-allocation profile remains unchanged even
though native Lean allocates MPZ storage beyond its small-Nat range.

## Reviewable implementation and validation

First extend the registry/descriptor/data representation and tests; load the small
namespaces in the existing resident before completing emitter work. Then extend
the common emitter/materializer with checked Nat arithmetic, RC no-ops and the
existing chunk bailout. Keep caller-frame support from the reviewed frame branch.

Use actual pinned exported Nat programs after inspecting their producer IR,
including real borrowed externs and inc/dec sites. The actual borrowed bounceA/B
producer bodies retain post-call dec instructions, so they are non-tail calls and
remain explicit unsupported controls. Do not erase their observable frames/RC or
claim actual mutual-Nat fast coverage from those fixtures. Test every small fuel prefix,
carrier classes, resumes/siblings, identity/constant/saturating-sub and genuine source tail shapes; preserve all dead locals and saved caller state. Prove specialized work
occurred before a later overflow and prove fallback starts at the current entry.
Test MAX-1/MAX/MAX+1, literal/range/carrier rejection, MPZ/RawNativeScalar entry,
negative-input charged failures, redefinitions, cache/version edits and budgets.
Retain separate interpreted borrowed/owned MPZ controls without changing policy.

Measure preparation, Pattern/eval and warmed execution separately; report the
promotion-fallback path separately from successful loops. No repeated Init,
Source bootstrap or additional interpreter is needed. Native mathematical value
and ABI oracles are independent from hosted snapshot/allocation parity.
