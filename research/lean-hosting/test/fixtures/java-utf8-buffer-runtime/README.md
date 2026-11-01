# Original UTF8 and buffer family

Pinned Lean819816b2e0a3bf405af45ae5c7af2491d8f5bee6. The bounded collector
hashes all120,853,740 accepted index bytes while parsing375,258 declaration
pairs, derives419 ByteArray-segment Names, checks the complete candidate SQLite
domain, then authenticates raw CAS bytes/typed Names. This fixture preserves
five genuine extern declarations and their five genuine boxed wrappers, removing
only top-level pretty text. The complete17-extern ByteArray inventory remains
metadata; only the existing family and the two new buffer symbols are supported.
The three String conversion declarations correspond to two native symbols.
See provenance.edn for input/source/output hashes and exact original rows.

Sources: runtime/object.cpp2076–2092 and2551–2648; runtime/utf8.cpp223–275;
Init/Data/ByteArray/Basic.lean135 and the original String definitions. Native553
registers both lean_string_to_utf8 ABIs: String.toByteArray owns its String,
String.toUTF8 borrows it. Both produce a fresh RC1 ByteArray with live size and
capacity equal to the UTF8 byte count, excluding any C terminator. All bytes,
including embedded NUL, survive. Output storage never aliases the existing weak
String UTF8 cache. A primitive final Function ABI flag preserves the distinction
at every root/closure/admission guard without relying on declaration names.
Java String values have no guest RC; this does not simulate native String heap
allocation, capacity, ownership counters or physical identity.

Native555 implements the exact strict validator over LIVE bytes: valid1–4-byte
Unicode, no overlongs, surrogates, values above10FFFF, malformed continuations or
truncations. Native554 implements the valid-Unicode JVM subset of unchecked
conversion: erased proof0 and valid bytes are required BEFORE ownership release.
Native unchecked String storage can contain malformed bytes; java.lang.String
cannot preserve that representation. Such input is rejected, not decoded lossily.
Unpaired Java UTF16 surrogates are similarly rejected before any new conversion
can fill or return a lossy UTF8 cache. String/ByteArray output is bounded to16MiB.

Native556 preserves native sourceOffset→length→destinationOffset evaluation.
The size_t domain is mathematical0..2^64−1; beyond-domain Nats reject instead of
native OOM. Source offset greater than live size returns the destination before
reading the other two Nat values. Otherwise length clamps to source availability,
destination offset clamps to destination live size, and size=max(old,offset+len).
Capacity grows only when required, to newSize when exact or2*newSize otherwise;
then nonexclusive buffers copy at that capacity. Even a zero-length operation
copies a shared destination. New allocation/capacity/Bool validation finishes
before mutation or destination DEC; validated leaf releases cannot call guests.

The pinned implementation uses memcpy and assumes nonoverlap after exclusivity,
not a general memmove contract. Real boxed equal source/destination arguments
need separate owned credits and therefore COW; RC0 persistence also COWs while
preserving source lifetime. The narrow one-credit alias model supports zero or
disjoint regions only when an exclusive destination reuses existing capacity.
It rejects overlap and copies that would destroy its own borrowed source. This
is an explicit native-safe subset, not a claim that every alias is invalid or
that Java reproduces native UB. Source/destination values never gain fake credits.

Raw borrowed String.toUTF8, ByteArray.validateUTF8 and ByteArray.copySlice require
proper original owned wrappers or valid original direct FAP sites. The owned
String.toByteArray origin remains callable and capturable. Guards cover ROOT,
PAP, makeClosure, imported closures, closure acceptance and AP/Host ingress.
New native IDs are553–556; stdio545–552 is a separate unit. No common Node fields,
guest-valued metadata, external capabilities, ready task state or source aliases
are added.

Twenty focused test families are prepared, each behavioral group covering both
interpreter drivers. They exercise original wrappers/ABIs, Unicode/NUL, invalid
classes and proof, cache separation, capacity and logical sizes, exact/geometric
COW, alias domains, size_t ordering, persistent buffers and forks. Deliberate
unsafe alias failures remain terminal; tests do not claim generic failed unwind.
The author performed bounded metadata collection and source/delimiter/arity/diff
audits only. No author JVM/native execution or complete frontend success is
claimed. Root must compile the frozen Java source and run definitions plus
focused/regression gates before a new runtime cohort is admitted.

## Coordinated validation

Root compiled the unchanged source with Java11 compatibility and loaded a fresh
isolated ClassLoader in the SAME retained384MiB REPL. Final focused-v3 passed
20 tests /784 assertions with no failures/errors; each behavioral family covers
both drivers. Runtime source SHA256:
`e59cab0ef21f19fbc553d3da622814c71f9e90b1a0aa14962b8947f5cb8f502c`.
Tested jar SHA256:
`0ebad4888584a5316a8012b8051071ad7f93cae72583960137231f07420b1124`.
External focused log SHA256:
`413040fbad2a693ba6341bd7cb487578bde57657b2dc2d0fc6146b18dbd678fc`.
The initial runs exposed only fixture mistakes (qualified Name construction, a
negative ABI case that was actually the other supported signature, and Integer
capacity from count); no runtime source changed. The corrected malformed-byte
case also passed independently:1 test /192 assertions. Full interpreter regression,
stdio integration and a new admitted frontend runtime cohort remain subsequent
gates; this tiny focused success does not imply those outcomes.
