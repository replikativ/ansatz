# Raw binary64 lane and original Float runtime

The experimental Java interpreter has a distinct F64 lane (5) for raw IEEE
binary64 words. Registers, results, frames, joins, self-tail scratch, nullary
caches, scalar payloads and Float boxes move raw long bits. Float literals convert
an arbitrary Nat numerically to nearest binary64; they do not reinterpret or
truncate it to 64 bits. The matching-native oracle explicitly exercises native
Float.ofNat, including rounding ties above 64 bits and overflow neighbors.

Nine original roots (eight symbols) are supported: Float.ofBits, Float.ofModel,
UInt64.toFloat, Float.sub, Float.mul, Float.div, Float.beq, Float.decLt and
Float.toString, with all nine original boxed wrappers. ofBits/ofModel canonicalize
NaNs to the target-verified quiet pattern `0x7ff8000000000000`. Unsigned UInt64
conversion uses the whole unsigned magnitude. Java 11 strictfp arithmetic keeps
separate guest operations at binary64 precision; it does not contract them into
FMA. Comparisons use primitive double `==` and `<`, including unordered NaNs and
equality of signed zeros. Arithmetic NaN payload/sign parity across native/JVM
implementations is outside the claim.

The physical Float box is the upstream tag-0 constructor with no object fields
and eight scalar bytes. It shares its physical layout with USize and UInt64;
typed IR chooses interpretation. No artificial boxed-lane tag is added. SProj
and SSet allow Float at the existing exact byte offset, including unaligned
access, and preserve ordinary bounds/exclusivity/kind guards. UProj/USet stay
USize operations. F64 CASE rejects during preparation, including unexecuted
alternatives. UInt16 and Float32 remain descriptive Header metadata with no
execution support; scalar graph-global import remains unsupported.

Public scalar inputs, results, request views and Host replies use Double only.
Long/BigInteger are never coerced into Float parameters, and Double is never
admitted as an OBJ value. Java's Double bit-conversion contract can quiet a
signaling NaN at a public boundary; no public signaling-payload guarantee is made.
Internal code and host suspension store a private immutable F64Bits value in
lane-typed control packets, before any conversion to a public view. Inspection
creates defensive Double views and never replaces the saved bits. Resume reads
the saved word directly, and forks share that immutable packet value. It owns no
guest values and cannot enter guest arrays, closures, graph recipes or public OBJ
replies. A supplied Double in an external fork-root vector may remain an immutable
diagnostic snapshot; that remapping confers no OBJ admission. Public root entry
validates Double strictly; private entry consistently decodes typed saved packets.

Float.toString targets the observed pinned producer's C-locale, nearest/even,
six-decimal std::to_string behavior. It emits NaN, inf and -inf as verified by the
matching native runtime. Finite values use the exact BigDecimal(double)
constructor, HALF_EVEN scale six and plain decimal text, retaining a negative
sign whenever a negative finite input rounds to zero. This includes negative
subnormals, not just -0. No system locale or floating environment controls Java
formatting. Pinned CMake source selects C++20 and disables FP contraction.

The bounded oracle feeds 278 runtime vectors to a matching installed Lean 4.33.1
binary. A read-only query shim observes FE_TONEAREST and LC_NUMERIC=C in that
same process; all Float operations still execute the actual Lean runtime.
The receipt pins the executable, shared runtime and C library. That evidence
supports this concrete observed formatter, not every libc/locale/FENV profile,
and does not prove this binary generated the accepted producer checkpoint.

Tests cover all original roots/wrappers, native arithmetic/rounding/formatting
vectors, typed rejections, raw signaling-word transport, joins/tails/cache,
scalar AP boxing, aligned/unaligned fields, request inspection, fork/resume,
preclaim invalid Host replies and postclaim overapplication failure ownership.
The original MessageData formatting bodies and full header corpus remain the
campaign's separate integration gate. No full official frontend completion,
Float32, broader Float family, native FFI, raw public Float codec or general
floating environment compatibility is claimed here.

[Fixture, native oracle and provenance](../test/fixtures/java-f64-runtime/README.md).

The integrated isolated jar gate exits zero with 646 test executions / 20,657
assertions across 73 suites at 384 MiB. Independent architecture/source review
found no blocker and checked the fixture, oracle and pinned-source receipts.
Legacy unsupported-lane probes now use Float32. Invalid Double arguments to OBJ
functions reject at the typed entry boundary, including Nat-operation probes.

All twelve existing native header-oracle cases now complete and match hasErrors,
UTF-8 headerEndByte and rendered diagnostic content in the retained 384 MiB REPL.
The file shim returns Message.toJson structures, while the older parser oracle
stores rendered messages. The comparison explicitly projects fileName, line,
column, severity and data to that rendering and requires empty captions for these
cases; it does not rewrite either golden or claim equality of different schemas.
Cases run in separate graph forks from the same compiled baseline and demand
additional original bodies as needed. This is header compatibility, including
error paths, not command elaboration, execution of declarations or self-hosting.

## Ordered less-than-or-equal

`lean_float_decLe` (native ID543) uses Java's binary64 `<=`, following pinned
`src/include/lean/lean.h`, whose implementation is `return a <= b;`. It returns
false for every NaN operand, including signaling/quiet payloads and negative NaNs;
positive and negative zero compare equal. It does not use `Double.compare`,
which imposes different ordering on zeros and NaNs. This extends explicit Float
intrinsic membership without changing the existing raw binary64 carriers or
UInt64/Float32 lane guards.

The captured `Float.decLe` row is all-owned `[float,float] → uint8`. Its original
all-owned boxed wrapper is `[object,object] → tagged`, performs the original
unbox/DEC sequence, then boxes the comparison result. Both actual source rows
and pinned source file hashes are in `test/fixtures/java-float-le-runtime/`.
The focused checks compare raw, FAP, raw-word stack transport, genuine boxed and
PAP/AP paths against an independent integer IEEE encoding oracle, including
signed zeros, infinities and several NaN payloads. They also verify transferred
box ownership and unchanged payload bytes, numeric Float literals versus raw
word reinterpretation, and exact typed/borrow ABI rejection. The check runner
runs the suite with both drivers. No new native oracle was executed for this
addition; the native claim is source equivalence within the existing IEEE
binary64 profile, not evidence about floating exception-status flags.
