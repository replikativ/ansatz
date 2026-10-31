# Bounds-safe ByteArray.get!

Intrinsic557 admits the original `lean_byte_array_get` ABI: borrowed object and
borrowed tobject Nat, returning uint8. The exact original ByteArray.get! extern
and compiler-generated owned boxed wrapper are frozen in
`test/fixtures/java-byte-array-get-default/`, with raw CAS SHA256 provenance.

Pinned Lean819816b2e0a3bf405af45ae5c7af2491d8f5bee6, lean.h1182–1190,
returns the unsigned live byte for an in-bounds scalar Nat and0 otherwise.
An MPZ index cannot be in bounds in the native valid representation. The JVM
profile compares its admitted mathematical Nat against the bounded logical size
before narrowing, so huge BigInteger indices return0 without wrapping. Spare
capacity does not count as live data. Invalid Nat carriers and dead/foreign/
malformed ByteArrays remain errors. Neither argument is consumed by the raw
primitive; the authentic boxed wrapper owns and decrements its arguments.

The proof-based `lean_byte_array_fget` remains intrinsic201, retains its erased
proof argument and bounds failure. The new operation shares realm/kind/live-size
validation and borrowed entry/closure guards, but has its own zero-default branch.

Focused checks are in `byte-array-get-default-checks.clj`. Load after the existing
baseline and byte-array check namespaces, then bind the newly compiled basis:

```clojure
(binding [java-ir-byte-array-get-default-checks/*basis* actual-new-basis]
  (java-ir-byte-array-get-default-checks/check!))
```

Five test families cover original pins/exact ABI refusal, live bytes/out-of-range/
huge indices, spare capacity and RC/counters, raw borrowed entry/closure refusal,
and dead/foreign/wrong-kind/malformed metadata. The worker performed reader and
source checks only; root owns JVM compilation/focused/full validation. No native
compiler/exporter process or worker JVM was launched for this change.
