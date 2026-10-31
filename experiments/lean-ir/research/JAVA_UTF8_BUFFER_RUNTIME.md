# UTF8 and buffer runtime profile

This unit supplies native553–556 for original String UTF8 conversion, ByteArray
UTF8 validation and copySlice, based on Lean819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
It is independent of the545–552 stdio unit and changes neither kernel APIs nor
artifact source policy. The runtime accepts proper original raw ABIs and boxed
wrappers rather than rewriting a blocked caller or returning a guessed value.

The Java backend's supported Strings are valid Unicode. Encoding rejects
unpaired UTF16 before allocation or cache mutation. Validation is exact for
pinned strict UTF8 and inspects only ByteArray live bytes. Unchecked decoding is
supported only after strict validation; malformed native String storage cannot
be represented by java.lang.String and rejects before consuming its ByteArray.
Embedded NUL is data, not a terminator. Conversion buffers copy bytes and never
expose the immutable String UTF8 cache. Maximum ByteArray/encoded extent is the
existing16MiB bound; native OOM and physical String/MT/storage parity are unclaimed.

copySlice preserves native unsigned64 conversions, evaluation/early-return order,
clamping, exact versus geometric growth, and capacity/exclusivity COW ordering.
The destination's only owning release is quiet because ByteArray metadata owns
no guest values. An original boxed equal-source/destination call has separate
credits; COW keeps the borrowed source alive. A one-credit same-object model is
accepted only for native-safe exclusive, no-allocation, zero/disjoint copies.
Overlap or a copy that would retire its borrowed source rejects before effects.
The source uses memcpy; this unit does not extend its contract to unsafe overlap.

A final per-Function borrowedUtf8 flag distinguishes the two signatures of
lean_string_to_utf8. This is immutable ABI metadata; it adds no Node field and
retains no extra source/engine graph. Borrowed String conversion and ByteArray
operations are fenced at owning root/closure admission; owned String.toByteArray
and genuine boxed wrappers remain usable. Owned conversion preflights also run
before saturated AP capture/closure transfer in both drivers.

The exact ten-row fixture, complete ByteArray extern inventory, source pins and
reproducer are in test/fixtures/java-utf8-buffer-runtime. Twenty focused tests
are defined in research/java-ir-baseline/utf8-buffer-checks.clj. At this source
checkpoint they have not been executed by the author; no full source loading,
stdio integration or new frontend cohort success follows from these definitions.

Coordinated root validation now passed all20 focused families /784 assertions on
the same frozen source, in an isolated ClassLoader inside the retained384MiB REPL.
Validation hashes and the fixture-only initial corrections are recorded in the
fixture README and validation.edn. Author source/metadata work launched no JVM or
native runtime. Full158-group regression and combined stdio/frontend acceptance
remain root integration gates; old hosted-file acceptance is unchanged.
