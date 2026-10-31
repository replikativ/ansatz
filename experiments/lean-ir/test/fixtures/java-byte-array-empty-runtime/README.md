# Empty ByteArray native profile

Pinned source: Lean `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
`Init/Prelude.lean:3437` declares `ByteArray.emptyWithCapacity` using
`lean_mk_empty_byte_array`. `include/lean/lean.h:1170` borrows the capacity Nat,
panics out of memory for a non-scalar capacity, and calls
`lean_alloc_sarray(1, 0, lean_unbox(capacity))`. The allocator stores independent
live size and capacity. Native allocation does not promise zeroed spare bytes.

The accepted original raw row is
`adcec717e8278218a20186c21ea0f4a32876d8c72f3979abac9800ff6bf0afb2`,
with `[tobject borrowed] -> object`. Its original owned boxed facade is
`e5da3a13f74db5a4f0af4913e494e02442399f2b5b6df883c814be262bbd1090`;
it calls the raw function and decrements only its owned capacity occurrence.
The observed `ByteArray.empty._closed_0` body is also preserved unchanged.
Only top-level pretty text is removed in the fixture; the generator authenticates
the actual complete accepted index byte stream and its SHA, then each exact typed
Name/hash membership and original raw CAS bytes before creating it. SQLite is
only a candidate accelerator and must match the index-derived domain exactly.

Native 544 uses the existing raw ByteArray tag248/kind metadata, allocates live
size zero with exact requested capacity, and borrows the argument. Validation
finishes before allocation or guest ownership changes. Supported capacities are
0 through the existing 16 MiB ByteArray capacity bound. Higher capacities reject
with a bounded-profile error, rather than attempting native OOM behavior. This
includes all canonical native heap Nats (values above signed63 on the pinned
64-bit profile). Java Long/BigInteger are immutable Nat carriers; a small-valued
BigInteger denotes the same scalar-domain value, not a forged native MPZ object.
No address bits, native OOM, unspecified spare bytes or MT headers are simulated.

Raw borrowed external entry, raw closures/PAP/imported closures continue through
the shared borrowed-ByteArray fences; callers use the original owned boxed
wrapper or a proper original direct FAP. Existing push, copy-on-write, logical
RC and fork mechanisms apply without special cases. Both interpreter drivers
reach the new ID through explicit BYTE_EMPTY dispatch outside the old200–203
range. No native implementation or kernel API is replaced.

## Remaining original extern inventory

`extern-inventory.json` authenticates all17 accepted extern rows whose typed Name
is under ByteArray. Five now have native symbols implemented: mk, empty allocation,
proof-backed get, size and push. Twelve rows remain unsupported: data conversion,
get!, uget, usize, set!, proof-backed set, uset, hash, copySlice, beq, decEq, and
UTF-8 validation. `beq`/`decEq` share `lean_sarray_dec_eq`; their exact raw ABIs are
recorded, including proofs and borrow flags. Presence in this inventory does not
authorize a stub or infer an implementation from a similar symbol.

`string-conversion-frontier.json` additionally pins String.toByteArray/toUTF8
(`lean_string_to_utf8`) and String.ofByteArray
(`lean_string_from_utf8_unchecked`). These are plausible subsequent boundaries
when an original frontend path encodes/decodes bytes: Prelude's List.toByteArray
builds with empty+push, and String's original representation conversions use these
symbols. This is a source-based candidate frontier, not a prediction of the next
Nat numeral call or proof that this whole path is runnable. The actual caller
stack and next real Code/Host boundary must determine further work. In particular,
unchecked UTF-8 conversion needs its own native source/ownership/invalid-byte audit.
This patch implements only empty allocation.

## Reproduction and checks

Run `collect.py REVIEWED_ROOT LEAN_REPOSITORY` with explicit paths to the accepted
catalogue/CAS metadata and the readonly pinned source checkout. The bounded
reader hashes all120,853,740 index bytes while parsing375,258 declaration pairs;
it derives419 ByteArray-segment Names independently of SQLite, authenticates
every domain CAS row to find the complete17-extern inventory, and checks all
three requested String conversions against that same index. The fixture, extern
inventory and String conversion outputs are byte-identical after this stronger
audit. The collector enforces a256MiB address-space cap,90s CPU cap,60s index
scan deadline,160MiB index limit,16MiB parser buffer and500,000 declaration
limit. It performs no native/guest execution and records index counts and
source/blob/inventory hashes in provenance.edn.
`byte-array-empty-checks.clj` defines seven focused tests: exact ABI refusals,
size/capacity/RC, authentic empty body and owned PAP/AP, spare-capacity push reuse,
shared COW and fork independence, invalid/over-profile rejection before allocation,
and borrowed raw entry/closure fences. Test capacities stay tiny; no16MiB buffer
is allocated. Each behavioral family covers both interpreter drivers.

The author ran source/CAS/hash/delimiter/diff audits only. Root must compile a new
immutable runtime jar, load it with an isolated ClassLoader, and run
`(java-ir-byte-array-empty-checks/check! basis)` plus existing ByteArray, ownership,
fork and focused native gates before admitting a new runtime cohort. Old jar and
cohort remain valid. No JVM/native execution or fresh frontend success is claimed
by this fixture.

Coordinated validation compiled a frozen Java 11 jar and loaded it through a new
isolated ClassLoader in the retained 384 MiB REPL: seven tests and 168 assertions
passed. The complete interpreter gate passed separately in 384 MiB: 157 groups,
1,494 tests and 59,210 assertions, zero failures/errors. Its log SHA256 is
`0f954834cfa5df6e4c2b7fd10175a3bd0c55bb1b74d1c6f6996372f604b6442a`.
The runtime source SHA256 is
`9980ba8298f6dd09db1da806b4b6dbda848f1d746c89655de60467cb05fe721f`;
the tested jar SHA256 is
`cfe1ff1bfd51c4e7c8e5f688117e9c70e214ff18d760fbc69c1b56d554aac23d`.
This validates the original empty-ByteArray caller, not the full Nat-arithmetic
frontend route, which still requires a new admitted runtime cohort.
