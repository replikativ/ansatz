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
capacity does not count as live data. Invalid Nat carriers and dead/wrong-kind/
malformed ByteArrays remain errors. Neither argument is consumed by the raw
primitive; the authentic boxed wrapper owns and decrements its arguments.

The proof-based `lean_byte_array_fget` remains intrinsic201, retains its erased
proof argument and bounds failure. The new operation shares realm/kind/live-size
validation and borrowed entry/closure guards, but has its own zero-default branch.

Focused checks are in `byte-array-get-default-checks.clj`. Load after the existing
baseline and byte-array check namespaces, then bind the newly compiled basis:

```clojure
(java-ir-byte-array-get-default-checks/check!
  actual-new-basis "test/fixtures/java-byte-array-get-default")
```

Eight test families cover original pins/exact ABI refusal, live bytes/out-of-range/
huge indices, spare capacity and RC/counters, raw borrowed entry/closure refusal,
ordinary same-class owned transfer, and dead/wrong-kind/malformed metadata. The worker performed reader and
source checks only; root owns JVM compilation/focused/full validation. No native
compiler/exporter process or worker JVM was launched for this change.

The fixture directory argument may point into the isolated worktree while the
retained REPL keeps its normal baseline working directory. The malformed-size
case starts from an actual tag248 ByteArray, unwraps its genuine ByteArrayState,
then temporarily sets logical size beyond capacity. Ordinary ByteArrayState has
no per-interpreter realm marker: a same-classloader ByteArray may be explicitly
transferred into another internal engine, where the actual boxed wrapper consumes
that owner. This is not general permission to cross runtime-specific protected
value boundaries. Dead and malformed cases verify rejection and unchanged RC
before restoring test-only corruption and retiring any remaining local owner;
they do not claim recovery of arbitrary failed callback/task ownership.

The parent compiled the frozen Java source once (`javac -J-Xmx384m --release 17`)
and ran it in the retained 512 MiB JVM. The corrected focused gate passed eight
tests/53 assertions; existing ByteArray regressions passed thirteen tests/118
assertions, for 21 tests/171 assertions with no failures/errors. Only test sources
were reloaded after the first failed model assumption; Java remained unchanged.
The earlier five-test run had45 passes, two failures and one cleanup error because
it incorrectly expected same-class ordinary ByteArray transfer to reject. That
history remains recorded in byte-array-get-default-validation.json rather than
being described as a runtime defect or a successful gate. No full combined gate,
entropy implementation or actual Random initializer execution is claimed here.
