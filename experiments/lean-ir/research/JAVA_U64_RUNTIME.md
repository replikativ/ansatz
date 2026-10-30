# Distinct UInt64 lane and original hash runtime

The engine adds a UInt64 lane while preserving existing lane IDs, including a
separate USize lane. Both occupy raw64-bit numeric slots; typed arguments, joins,
returns and stores still require exact lane agreement. UInt64↔USize conversion is
explicit. Public input/reply values are exact nonnegative integers through2^64-1;
high-bit outputs become positive BigInteger. Internal bits are never revalidated
as negative mathematical inputs during frames, tails, caches or forks.

Pinned Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` converts IR
Nat literals modulo2^64. This differs from public scalar range checking: literal
2^64+7 becomes7, while the same host UInt64 argument rejects. UInt64 always boxes
as ctor0 with zero object fields/eight scalar bytes, even zero. Packed SProj/SSet
retain full word-relative offsets, exclusivity and byte bounds; USize continues
using its separate UProj/USet paths. Wide scalar cases outside unsigned32 remain
explicitly unsupported, matching the existing bounded USize policy rather than
silently adopting the native interpreter's32-bit truncation.

Ten genuine inventory declarations and their ten boxed wrappers execute:
String.hash, mixHash, UInt64.ofNat/ofNatLT/ofBitVec, shiftRight, xor, toUSize,
decLt and decEq. Borrowed and owned Nat conversion ABIs remain distinct. Shift
counts mask modulo64; right shift is logical; comparison is unsigned. Float
bridges and Expr.mkData packing remain separate. Their authentic rows are retained
as metadata in the broader28-row fixture, without claiming execution support.

String.hash is pinned MurmurHash64A over exact UTF-8 payload bytes with seed11,
little-endian blocks and64-bit wrapping. mixHash intentionally differs: its
second key step XORs the multiplier constant, instead of Murmur's second multiply.
This distinction is necessary for genuine Name hash compatibility. Name hash is
computed and stored by its original constructor override bodies, not replaced
with Java identity/hashCode or catalogue SHA256 hashing.

The [fixture](../test/fixtures/java-u64-runtime/README.md) includes an independent
compiled pinned hash-source arithmetic oracle. Exact upstream hash.cpp/hash.h are
compiled with minimal type/include scaffolding on a64-bit little-endian host.
All sixteen vectors agree with the separate integer reference. This validates
that arithmetic, not the complete Lean runtime ABI/heap. Result/source digests are
checked against provenance before vectors are used. The native compiler is a
reproduction tool; it is not a Java runtime or default-test dependency.

Ten tests /220 assertions pass per driver. They cover literal wrap, caches,
strict lanes, joins, self-tail calls, AP boxes, mixed packed fields and forked
stores; host/code-request high-bit arguments/results and invalid-reply retry;
primitive hashes; and the eleven-row genuine Name.str/num/hash closure including
seed1723 and the large-numeric-name sentinel17. The previous unsupported-lane
metadata test now uses still-unsupported Float. Independent source/ABI/transport
review is clear after strengthening oracle digest checks. The isolated jar gate
passes494 executions /16,820 assertions across59 suites at384MiB.

The six-global original header probe advances to72 original bodies /2,131
instructions and stops at ptrAddrUnsafe in Name.quickCmpImpl. Correct pointer
identity, ByteArray state and the larger code/data/global fixed point remain
separate researched gates. No complete parser, elaborator, physical-pointer ABI,
Float execution, public frontend bundle or self-hosting claim follows.
