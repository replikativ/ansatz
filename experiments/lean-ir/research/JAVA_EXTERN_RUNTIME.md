# Captured extern ABI and first runtime expansion

This extends the research Java interpreter, not the public loader or runtime
defaults. It implements the first bounded part of the
[IO runtime agenda](JAVA_IO_RUNTIME_PLAN.md).

## ABI recognition and execution

An immutable registry describes the selected C symbol, exact captured IR
parameter/result types, borrow bits and implementation ID. It covers eight
executable Nat intrinsics and two captured signatures for `lean_usize_of_nat`.
The USize signatures are recognized but not executable: preparation still
rejects USize lanes. The research-only `validateExternAbi` method validates ABI
recognition, not preparation, source admission or execution support.

Preparation uses that same resolver. It checks exact raw IR types in addition
to physical lane validation, preserves erased parameters and rejects missing or
changed borrow flags. It preserves first matching `all`/`c` backend selection;
other backends are skipped. Unsupported inline entries and symbols reject.
Registry lookup runs only during preparation/inspection. Execution retains
pre-resolved integer dispatch. This is a closed intrinsic registry, not yet a
general host callback/capability interface.

## Nat operations

The new operations execute original captured `Nat.mul`, `Nat.div` and `Nat.pow`
declarations. They follow Lean 4.33.1 commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:

- `src/include/lean/lean.h`, `lean_nat_mul` and `lean_nat_div`: exact natural
  multiplication with promotion; division by zero returns zero.
- `src/runtime/object.cpp`, `lean_nat_big_div`: the same zero-divisor rule for
  large operands.
- `src/runtime/object.cpp`, `lean_nat_pow`: rejects exponents above `UINT_MAX`,
  including for bases zero/one. Binary exponentiation avoids Java
  `BigInteger.pow`'s signed-int exponent restriction.

Inputs are nonnegative Long/BigInteger Nat carriers; results normalize to Long
where representable. Negative/inexact inputs reject; `0^0` is one. Large results
remain subject to JVM resource/BigInteger limits.

Native exponent overflow is an internal panic terminating that invocation.
Here it is a runtime trap, not an EIO error value or a process exit. An internal
explicit-driver error poisons its engine; managed failure cleanup remains
separate work. A direct intrinsic validation error precedes root publication.
Tests do not replay failed guest frames.

## Evidence

[NatExternOracle.lean](java-ir-baseline/NatExternOracle.lean) receives operands at
runtime. One pinned native invocation produced 288 multiplication/division/power
observations covering Long boundaries, large Nats, zeros and maximum accepted
exponents for zero/one. Another confirmed rejection of `pow,0,4294967296`, exit 1.
The [oracle receipt](../measurements/java-ir-nat-extern-oracle.edn) pins source
hash, producer revision, inputs/results and rejection output. Native IR
preference was disabled; extern primitives remained native.

Both Java drivers compare every result via direct extern entry and ordinary
guest wrappers. Tests cover both USize ABIs, borrow/erasure/result drift, backend
selection, recognition versus execution, negative Long/BigInteger operands in
both positions, and inexact values. The isolated engine-jar runner passes
42 executions / 2,711 assertions in a 384 MiB JVM, including previous value,
ownership, continuation and corpus checks.

RBMap main now has 18 unsupported extern declarations, down from 21. Its full
closure still fails U32 preparation; it is not executable. The
[new receipt](../measurements/java-ir-externs-2026-10-28.edn) retains the current
inventory separately from the earlier corpus evidence.

A paired retained-REPL RBMap1000/1001 control compared old/new jars in both
drivers, seven alternating batches of 100 runs after warming. Final CPU medians
were recursive 3.784/3.778 ms and explicit 9.157/9.412 ms per execution. Allocation
was equal at 1,515,868 bytes/run, including the host batch adapter. Preparation
was excluded. No separate local test process overlapped this final comparison;
the earlier overlapping control is retained as diagnostic evidence.

Shared-machine load and retained JVM compilation history limit precision. Both
old and new explicit drivers differ from the earlier fresh-process baseline.
These controls establish no allocation increase or large isolated regression,
not a speed improvement or a new comparison against Lean. No full Init,
Mathlib or frontend image was loaded.

Next: U32/USize lanes, boxing and packed fields, followed by conversion and
string/array operations. Host boundaries and valid guest stdout follow their
data prerequisites. Heap forking/managed cleanup remain a structural track.
