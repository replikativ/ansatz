# Immutable String and UTF-8 position runtime

This research profile implements thirteen additional String runtime symbols from
Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, alongside
six existing symbols. Their aliases cover twenty-five original extern declarations
and all twenty-five genuine boxed wrappers. The
[source fixture](../test/fixtures/java-string-runtime/README.md) retains the full
original inventory group of 31 declarations and 31 wrappers, including six
explicitly unimplemented declarations. Fixture membership does not imply support.

The new symbols cover safe atEnd/get/next/prev/isValid/extract, equality/order,
UTF-8 byte access, Char membership, scalar-character length and character
replacement. Existing push/append/ofList and proof-backed get/next remain in use.
Exact raw lanes, erased arguments and borrow flags are preserved. String.hash
(UInt64), memcmp, Substring equality, pushn, posOf and offsetOfPos are separate
runtime work. No UInt64-to-Nat cast or fabricated hash is supplied.

Strings remain immutable Java String carriers. UTF-8 operations validate Unicode
scalars and use byte positions, including embedded NUL. The existing per-engine
bounded UTF-8 cache avoids rebuilding the same input's bytes for each parser
character. This does not implement mutable native String capacity or guarantee
native allocation behavior. Lone Java surrogates reject rather than silently
becoming replacement characters.

Safe get returns Lean's default Char 'A' (65) for end, invalid continuation and
out-of-range positions. Safe next advances by one at/past end or at a continuation
byte, including arbitrarily large Nat positions. Prev clamps zero and otherwise
scans backward or subtracts one beyond the end. isValid accepts the end boundary.
Proof-backed operations retain their narrower valid-index domain.

Extract follows the pinned native behavior: invalid start produces empty;
continuation-byte end means the remaining suffix; ordinary past-end clips. If
either index exceeds the native small-Nat domain, the native implementation
returns the original String. This anomaly is confined to immutable String
carriers, without inventing new Node ownership semantics.

Equality and ordering compare unsigned UTF-8 bytes with exact lengths, without
Unicode normalization. Ordering returns lt=0, eq=1, gt=2. Java UTF-16 comparison
would differ for supplementary characters versus some BMP characters. Length
counts Unicode scalars; byte size counts UTF-8 bytes. Replacement may change byte
length and accepts embedded NUL while preserving the number of characters.

Six focused tests / 343 assertions pass per driver. They cover every byte
position in ASCII/NUL/multibyte inputs, valid fast positions, continuation/end/
past-end cases, huge Nat values, extraction boundaries, comparison, character
membership and variable-width replacement. Independent review checks semantics
against the pinned C++/header sources and original wrapper ABIs. The combined
isolated jar gate passes 434 executions / 14,708 assertions across 51 suites
at 384 MiB, including both invocations.

The demand-loaded original header program now reaches six loaded original bodies
and 242 IR instructions before the next missing runtime operation, Nat.decLe, in
a retained 384 MiB JVM. This is progress through file-map scanning, not complete
header parsing, file elaboration, kernel admission or self-hosting.
