# Atomic growth profile source changes

Source changes only: no new runtime acceptance receipt is implied. The production
runtime retains its existing bounded profile and adds guards to Nat.mul/Nat.pow,
String UTF-8 encoding, String.push/String.append and captured stdout/stderr.

Nat multiplication checks conservative operand-bit sum (16,777,216 bits) and
schoolbook bit-product work (2^40 units) before invoking BigInteger.multiply.
The work cap admits a pair of 1,048,576-bit operands but rejects larger products
on estimated work even when their result would fit. Products by zero/one avoid
allocation and retain exact semantics. The small Long path remains unchanged.
Power first retains the pinned UINT_MAX exponent admission, including bases
zero and one, then simulates the entire repeated-squaring sequence using bounded
bit/work estimates before the first multiply. Estimates can reject valid Lean
computations; accepted results are exact and never truncated. Guards and an
interrupt/deadline poll precede every multiply/square, and a final poll precedes
publication. Intermediate answers remain local until the primitive returns.

The native source authority is Lean commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6, src/runtime/object.cpp
lean_nat_pow lines 1616–1623; inspected with git show at that commit.

configureAtomicDeadlineAfterNanos accepts a positive relative duration up to ten
minutes. clearAtomicDeadline disables it; the raw default is disabled. Configure only at an open idle task-free boundary before
the next invocation. This is cooperative: a single JDK multiply/encoding/library
call is not preemptible. Result bounds are not hard JVM heap bounds; JDK
intermediates, caller strings and retained graph storage require additional heap.
RuntimeLimitException.code() is the value-only ResourceLimit or Cancelled code;
interrupt checks preserve the thread interruption flag. A terminal call retains
its actual engine ownership state and requires reviewed failure abandonment.

UTF-8 size/scalar validation precedes cache use and allocation. Push/append refuse
before concatenation beyond 16 MiB encoded bytes. Each captured channel has a
16 MiB UTF-8 total, copied with eager fork. drainCapturedOutput returns independent
immutable String snapshots at an open idle task-free boundary, resets both totals
and trims empty builders when their capacity exceeds 64 KiB. The owner must take
and release actual results before draining; failed branches retain their captures
until the reviewed failure lifecycle disposes or abandons them.

RuntimeResourceChecks.java is a standalone source-local regression intended for
the root's single JVM: compile with --release 11 against the freshly compiled
runtime, run with an appropriately bounded heap, then run the existing original-row
string, stdio, UTF-8, fork, arithmetic and explicit-lifecycle regression suites.
It covers arithmetic values, huge-exponent admission/refusal, overflow-safe work
estimation, cancellation/deadline classification, no result-slot publication,
invalid Unicode, exact UTF-8 sizing, output boundary, fork counters, and drain
snapshot ownership. A private-method test uses a BigInteger subclass that interrupts after its first
square, establishing deterministic cancellation at the next pow step without a
production callback hook. This subclass is test instrumentation, never an admitted
guest codec value; no timing-sensitive race is presented as evidence.

These guards are not a global heap or runtime proof. Existing array/byte-array,
String.pushn/set, expression and other intrinsic profile limits remain separate
and require their existing cohort tests. Native comparison establishes admitted
values, not worst-case allocation or preemption behavior.
