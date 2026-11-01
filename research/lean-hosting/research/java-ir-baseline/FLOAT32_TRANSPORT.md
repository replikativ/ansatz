# Float32 transport

The Java IR runtime represents `float32` as a distinct binary32 lane. Host arguments and results use exactly `java.lang.Float`; Float64, integer and object carriers are rejected. Suspension and fork copy preserve raw binary32 bits using immutable internal carriers. Boxed values and packed scalar fields occupy four bytes, matching the pinned Lean runtime. This supports preparing generic compiler helpers whose unexecuted alternatives contain Float32.

This change does not implement Lean’s Float32 arithmetic or conversion extern family. Reaching an unsupported primitive still fails explicitly. Float32 case dispatch remains unsupported. Nat literals convert directly to binary32 to avoid intermediate binary64 rounding.

The focused tests cover raw NaN payloads, signed zero, subnormals, infinities, packed unaligned storage, strict carrier rejection, joins, literal rounding, suspension and fork. Both ordinary and explicit runtime profiles pass. The complete regression gate passes on a 384 MiB heap: 162 groups, 1,549 tests, 60,527 assertions, no failures or errors.

Pinned source authority: Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, runtime `lean.h` Float32 box/unbox and scalar-field accessors.
