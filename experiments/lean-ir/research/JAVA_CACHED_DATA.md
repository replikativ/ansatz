# Borrowed Expr cached-data reads

The reached original `Lean.Expr.hasMVar` body calls `Lean.Expr.data`, an extern
with exact ABI borrowed object → uint64. Pinned Lean
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, lean.h3285–3287 implements it as
`lean_ctor_get_uint64(expr, lean_ctor_num_objs(expr)*sizeof(void*))`: the first
scalar word after the object fields. The Java Node stores fields and scalar
bytes separately, so this is scalar offset0, retaining all64 bits.

The implementation reads that existing word. It does not derive flags, recompute
hashes/depths, traverse the AST or allocate/copy/retain/decrement guest values.
Existing typed UInt64 transport preserves high bits in raw long storage and
positive public BigInteger views. No Node field or public API is added.

Authenticated original constructor IR establishes tags0–11 and object counts
`[1,1,1,1,2,2,3,3,4,1,2,3]`. Scalar semantic extent is8 bytes except lambda,
forall and let (tags6/7/8), whose extra BinderInfo/nondependent byte makes9.
The profile accepts those tags' 9-byte IR storage and verified native-aligned
16-byte storage. Unknown padding bytes remain untouched. It rejects other
layouts, immediates, dead nodes, closures, references, arrays, ByteArrays,
tasks/Promises and the existing invalid branch-owner cases. This is structural
storage validation; an unrelated constructor with an identical layout cannot
be nominally identified as Expr by these bits. Typed source provenance and valid
pure AST construction remain separate requirements. Cache words are not new
kernel admission authority.

Raw native root, PAP, makeClosure/imported closure, generic AP and host-reply
closure paths use the same borrowed-primitive fences as Name equality. Use the
authenticated original owned `Lean.Expr.data._boxed` wrapper at those boundaries.
It performs the original borrowed read, consumes its owned Expr input and boxes
the UInt64 result. A direct source FAP borrows its input without ownership effects.

There is **no new `lean_level_data` binding**. The actual accepted
`Lean.Level.data._override` is original guest fdecl code: zero returns its
computed cached constant2221; other cases project their stored scalar word.
The fixture retains that code and genuine constructors. Level.zero stays a
canonical immediate; no invented Level node/cache representation is introduced.

`test/fixtures/java-cached-data-runtime/` contains the complete bounded static
closure for selected genuine constructors/readers (46 rows, no initialized
dependencies), plus authenticated storage witnesses for all12 Expr constructors.
Tests execute genuine bvar/mvar/sort/app construction, high-bit loose-variable
range and hash packing, MVar/Level-MVar flag propagation, genuine Level zero/succ/
mvar reads, boxed AP, code/host suspension and fork. Separate explicitly modeled
storage tests exercise all12 layouts and nonzero padding without pretending those
model payloads establish semantic AST validity.

A bounded C++ oracle compiles the verbatim pinned cache getter and uint64 field
reader with clearly identified modeled object-storage API scaffolding. Sixteen
vectors vary object counts, high words and trailing bytes, checking read-only
behavior. It is a getter-offset oracle, not complete native allocation/object/RC
ABI evidence. Existing native-verified mkData/mkAppData packing and original
constructor IR provide the separate cache-construction evidence. Source/license,
original row hashes, fixture hashes and oracle provenance are retained.

Java11 compilation passed. Both drivers passed seven focused tests / 297
assertions each in the root's retained 384 MiB REPL. The isolated jar gate exited0
with 100 suites / 967 tests / 50,877 assertions; all100 footer positions match
observed suite counts in order. Source SHA256 is
`5d892bdeba775a0ad08007e488f6e91348b0c5151e49b7f0d42e3270ab846812`;
jar SHA256 is `1e8e0a2488aa7e919cd78bc84ef982492f5da340ceab058a64ffab035c166834`.
The source received an independent review with no blocker.

The genuine command crossed this cache-read boundary and reached 364,291
instructions / 1,331 demanded bodies, stopping at missing `Lean.Expr.eqv`.
The kernel adapter had not started and frontend execution remains incomplete.
Only bounded compiler/jar processes were launched by this feature worker;
focused execution used the existing retained interpreter JVM.
