# Integer arithmetic native differential

`Main.lean` exercises every Int, Nat and unsigned fixed-width (UInt8/16/32/64,
USize) extern that the SDK admits for ordinary arithmetic, at edge values: Long and
native small-Int (2^31) boundaries, 2^64/2^100 big integers, zero divisors, shift
distances at and beyond the width, and narrowing conversions. Operands depend on a
runtime seed, so the Lean compiler cannot fold them.

`Oracle.lean` prints `row i r 0` for every table `i` and operand row `r` with the
official `lean --run` executable. `expected.json` pins the SHA-256, byte and line
counts of that output for Lean 4.33.1 at
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

`test/arithmetic_acceptance.clj` reruns the native oracle, checks the pin, prepares
the same source with the packaged SDK and requires the concatenated JVM rows to be
byte-identical. `test/native_ci_checks.clj` runs it inside
`bin/lean-jvm-native-ci check`. One row per JVM call keeps each call inside the
Project instruction budget.
