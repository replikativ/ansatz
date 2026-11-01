# Immutable String and UTF-8 position runtime

The initial String tranche introduced thirteen additional runtime symbols from
Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, alongside
six existing symbols. Their aliases cover twenty-five original extern declarations
and all twenty-five genuine boxed wrappers. The
[source fixture](../test/fixtures/java-string-runtime/README.md) retains the full
original inventory group of 31 declarations and 31 wrappers. Fixture membership
alone does not establish a complete native runtime profile.

Five completion bindings add memcmp, Substring equality, posOf, offsetOfPos and
pushn, with exact source lanes, erased proofs and borrow flags. The String suites
now exercise thirty original declarations and thirty genuine wrappers;
String.hash is covered separately by the UInt64/hash profile. No fixture body,
ABI or original source identity is changed.

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

## Proof-carrying String positions

The [modern position fixture](../test/fixtures/java-string-pos-runtime/README.md)
adds the original `String.Pos.set` and its genuine boxed wrapper, alongside
`String.decodeChar`, `String.Pos.next` and `String.extract` and their wrappers.
These positions erase to logical Nat byte offsets, not raw USize lanes. The
modern setter shares `lean_string_utf8_set` with legacy `String.Pos.Raw.set`,
but its exact ABI consumes String and position, takes UInt32 Char and an erased
non-end proof. The legacy three-argument borrowed-position ABI keeps its existing
safe invalid-index behavior.

Both execution drivers dispatch all four modern setter arguments before the
ordinary three-argument path. Erased proof, logical Nat, valid non-end UTF-8
boundary and Unicode scalar validate before narrowing, output construction or
ownership effects. Replacing a character may change byte width, supports NUL,
and caps the resulting UTF-8 payload at 16 MiB. Invalid modern proof/index inputs
reject explicitly; they do not inherit legacy setter's return-input fallback.
Strings remain immutable Java leaves, so native exclusive ASCII in-place identity
and native allocation behavior are not claimed.

Fast get/next now also check their erased proof placeholder. Their existing
valid-index domain remains; extraction retains its pinned shared native behavior.
Raw borrowed fast get/next/extract require original owning wrappers at external
root, PAP, makeClosure and prepared-closure boundaries. Direct internal FAP
preserves each original borrow ABI. The genuine wrappers supply ownership and
Char boxing; no body or original row hash is rewritten.

Pinned sources: Init/Data/String/Defs.lean:352–360 (Pos); Basic.lean:786–789,
:1152–1154, :1665–1667 (extract/decode/next); Modify.lean:34–42,:160–166
(modern versus legacy setters); runtime/object.cpp:2468–2495 and
include/lean/lean.h:1350 (native replacement).

Ten focused tests pass from a separately compiled Java 11 jar in a retained
256 MiB REPL: 248 recursive and 269 explicit assertions. They cover original
ABIs/wrappers, Unicode and byte-offset matrices, invalid/high-bit/huge Nat inputs,
proof and owner preflight, output-cap refusal, borrowed entry fences and forked
boxed partial applications. Existing String, completion and baseline tests also
pass in both drivers. No Init/image or command elaboration was run for this
isolated change; those acceptance receipts remain separate.

## Range, Substring and repetition completion

`lean_string_memcmp` has seven exact arguments: borrowed String/String/Nat/Nat/Nat
and two erased proofs, returning uint8. Both execution drivers dispatch all seven
arguments explicitly. Complete raw UTF-8 ranges and proof placeholders validate
before index narrowing or ownership effects; continuation-byte ranges and empty
ranges at end are valid. Raw borrowed root, PAP, makeClosure and imported-closure
entries require an owning original wrapper.

`lean_substring_beq` consumes two ordinary tag-0 constructors with String/start
Nat/stop Nat fields and no scalar payload. It validates both operands before
consuming either, repairs each invalid endpoint to that String's end, and compares
the represented content; inverted ranges have zero Nat byte size. Shared,
persistent and duplicate container aliases retain their exact owner obligations.
Transient validated views remain local to a call.

Substring repair differs from legacy extract's nonscalar-index shortcut:
Substring.Raw over "aé" with start 1 and huge stop represents "é", while the
pinned native extract with a huge endpoint returns its original String. The
intrinsic implements the original Lean-exported repair/substring logic.

`lean_string_posof` consumes String and scalar Char and returns the first matching
UTF-8 byte offset, or byte length when absent. `lean_string_offsetofpos` consumes
String and Nat position, counting character advances until that byte position or
end; continuation positions round to the next character index and huge positions
yield character length. Neither result uses UTF-16 indexing.

`lean_string_pushn` consumes String, scalar Char and Nat count. Zero repetitions
transfer the original String. Nonzero repetitions append the scalar exactly n
times. The explicit profile caps total UTF-8 output at 16 MiB, validating count
and output before narrowing, output allocation or ownership effects. Huge counts reject
instead of wrapping or looping. Unicode validity and Char validity are required
even for zero repetitions; other String operations retain their existing bounds.

Pinned anchors: runtime/object.cpp:2505–2515 (memcmp);
Init/Data/String/Substring.lean:448–465 (repair/equality);
Init/Data/String/Basic.lean:3074–3084 (substring comparison), :3024–3058
(offsetOfPos); Search.lean:194–196 (posOf); Defs.lean:216–224 (pushn). All refer
to commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

## Validation and limits

Six existing String tests cover ASCII/NUL/multibyte positions, huge Nats,
extraction, ordering, membership and replacement. Nine completion tests exercise
original wrappers, byte-range matrices, proof/range rejection, malformed operand
preflight, repaired Substrings, alias ownership/forks, position conversion and
bounded output. Both drivers run from a separately compiled Java 11 jar in a
retained 256 MiB REPL, without Init or a full image. Runtime progress receipts
are separate campaign evidence; these bindings alone do not establish complete
header parsing, elaboration or kernel admission.

After integration with Name equality, immediate deletion and explicit build
identity, the isolated jar gate passes 624 executions / 19,423 assertions across
71 suites at 384 MiB. Independent source/ABI/ownership review found no blocker.
The original header program still completes the default declaration-header input.
Eight valid cases from the existing 12-case native header oracle match exactly
on hasErrors, UTF-8 headerEndByte and diagnostics: empty input, imports, module
flags, Unicode comments/names, nested comments, CRLF, a declaration following
imports and BOM handling. Each case runs in a fork with the existing compiled
baseline; additional requested bodies still materialize from accepted sources.
Four malformed cases stop during diagnostic-body preparation at the unsupported
Float lane. They are explicit compatibility gaps, not successful error output.
This corpus does not establish full command elaboration, project execution or
self-hosting. Single shared-machine case times are not a native-speed benchmark.

Integration evidence (2026-10-30): the complete standalone jar gate passes
704 test executions / 21,433 assertions across 77 suites, with a 384 MiB heap.
The existing native-output main checks now enter the original owned boxed
get/next wrappers; invalid proof/position cases use separate fresh engines in
the position suite because an in-wrapper failure is terminal in explicit mode.
The runner also checks both added suites in its expected-count contract.

The retained command probe executes the original `compileImportedFileState`
with a genuine fresh guest environment and `prelude\naxiom HostedSort : Sort 1\n`.
It advances to `IO.Promise.new` after 512 newly demanded original bodies and
299,247 IR instructions. Its 44 initialized globals are authenticated companion
values and all external owners are included at fork. No declaration has been
published: pending tasks and promises require a separate active runtime profile.
