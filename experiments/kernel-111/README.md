# Issue #111: conversion-order investigation

This is an opt-in research experiment, not a default kernel change or a claim
that #111 is closed. Full Mathlib has not been reverified with the candidate.

## Verified official-release reproduction

Published as [Lean issue #16088](https://github.com/leanprover/lean4/issues/16088).

The [standalone upstream reproducer](upstream/README.md) now reproduces the
version contrast using only Lean source and freshly downloaded official SDKs.
No tracing instrumentation, FFI helper, replacement kernel object, Foundation,
Mathlib, exporter parser, or Ansatz code is linked into that reproducer.

All official archives match GitHub's published SHA-256 digests. Installed 4.32.1
and 4.33.1 executables/kernel libraries were also byte-compared with those
archives, confirming the earlier installed-toolchain baselines. The standalone
`n=24` declaration checks on 4.32.1 and exhausts the 100,000 cumulative kernel
heartbeat limit on 4.33.1, 4.35.0, and 4.37.0-nightly-2026-10-27. A small `n=4`
control checks on all four. A separate review agent approved the reproducer.
The exact Foundation proof also reproduces on all four official SDKs; three
repeats of the 4.32.1/4.33.1 contrast have stable outcomes/allocation counts.

## Exact input and native controls

The input is the 94,993,283-byte Foundation export described in #111, SHA-256
`ac77f75929e109a35e72ebe90466a6012c4a7d47c8924a95d2a32edf3dea845b`.
It was regenerated from Foundation `e00e7ffd2b3caa639b12171341acb9172ee96d26`,
Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`, and lean4export
`4e7915201d3f9f04470d9eae002fa695f7cdc589` using Lean 4.32.1. No declarations
were admitted with verification disabled in the measurements below.

The unchanged Ansatz kernel at `2191c02` reproduces the first reported OOM.
Before optimizing allocation, we compared conversion order against Lean.

| Kernel/control | Observation |
| --- | --- |
| Lean 4.32.1 (`f054605aea4b840552cca2e725580bffd1e1b704`) | Raw kernel replay accepts the full closure: 14,178 declaration-package checks, representing 15,340 constants. 19.19 s process time; 1,018,288 KiB peak RSS. The four reported theorems take 2–4 ms each. |
| Stock Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) | With a checked prefix, the first reported theorem reaches a limit of 1,000,000 C++ kernel check heartbeats after 2,197 ms and 20,639,109 allocation heartbeats. Peak process RSS 717,696 KiB. This is a deterministic timeout, not a logical rejection. |
| Instrumented Lean 4.33.1 | Same timeout and allocation count as stock; 2,534 ms. First 35,752 completed conversion events match Ansatz's bounded trace in phase, depth, result and visible term fingerprint. Fingerprints are truncated, so this establishes prefix evidence, not full trace or semantic equivalence. |
| Lean 4.33.1 with only #14806 reversed, **diagnostic control only** | The first reported theorem checks in 2 ms / 30,388 allocation heartbeats. Other kernel changes remain intact. Reversal restores a known unsound cache and must never be adopted as a fix. |

The controlled reversal isolates the performance difference to the cache change
in Lean commit `c181643429983ef2908315c1eb6a1ccdbaa66086` (#14806). It does not
justify undoing that correctness fix. Its removed equivalence manager combined
transitive caching with recursive congruence checks; the replacement uses plain
pair caches. The baseline data does not establish an Ansatz-only reduction-order
defect.

Native replay uses `Kernel.Environment.addDeclCore` directly, not the higher
environment's asynchronous declaration metadata. Kernel and allocation
heartbeats are separate counters; the former is reset explicitly before the
bounded target check. A trace-only type-checker object was built from the exact
4.33.1 source and linked against that release's runtime. Stock and instrumented
controls use the same parser and driver. The native timeouts are reported as
kernel outcomes, not inferred from the driver's process exit code.

## Small fixtures

`extracted-conversion.ndjson` is a 15,822-byte identity theorem abstracted over
the local context at the expensive type comparison. It requires the checked
Foundation dependency prefix. It reproduces the expansion without the rest of
the original proof: Lean 4.32.1 accepts it, while 4.33.1 reaches the bounded
kernel timeout. The parser round trip preserves Lean structural equality of its
type and value (binder display representations may differ).

`projection-model.ndjson` is a separate, Init-only synthetic model. It compares
two applications of a computed `Prod` projection; the iteration count is written
as `24` on one side and `Nat.add 24 0` on the other. Each iteration doubles
composition of an identity function. Congruence can compare the counts directly;
normalizing the applications first can do much more work. This model illustrates
the conversion problem; it is not itself evidence locating the version boundary.
The corresponding expression builder and false-proof checks are in
`test/ansatz/kernel/projection_congruence_test.clj`.

## Candidate and rejected trials

A trial preserving intermediate application-spine sharing did not solve the
case. Bounded conversion events were unchanged, while allocation/time did not
improve enough to justify the change. That trial was removed.

Unrestricted early application/projection congruence makes all four reported
theorems fast, but it also spends too long comparing an argument another theorem
normally discards. It is not the proposed default. A bounded probe sharing the
parent's caches was also rejected: child equalities obtained under its alternate
order could survive an aborted probe and affect later normal-order queries,
reintroducing history dependence.

The current candidate starts only for matching projections, projection-headed
applications, or applications of the same projection definition. A fresh checker
tries positive congruence with a maximum of 4,096 combined checking/reduction
steps. It copies local context, fresh-ID position, declaration safety, permitted
universe parameters, eager-reduction state and reduction transparency/allow-list.
Its inference, equality and reduction caches are private and discarded. Only
the original pair's successful boolean result returns to the parent. Failure or
local budget exhaustion falls back to normal order. Global fuel and interruption
still abort checking; probe work is charged even when abandoned. Charging does
not replace an exception already unwinding.

The opt-in and budget are fixed at checker construction. Enabling the candidate
changes reduction order intentionally; it is not claimed to reproduce the exact
Lean 4.33.1 trace. It does not restore transitive equality caching, bypass checking,
or add axioms. Before default enablement it needs further paired-kernel and
library verification, including a deliberate Mathlib reverification decision.

An isolated candidate run checks all 15,340 input constants with zero errors in
10.802 s replay time / 11.89 s wall time, with 684,504 KiB peak process RSS,
using a 1,000,000-fuel cap per declaration. All four reported theorems check in
1.20–1.49 ms in that run. The first troublesome
theorem, measured separately, checks in about 7 ms, 2,542 fuel and 4.4 MB allocated;
the unchanged kernel still has not finished at 100,000 fuel / about 489 MB
allocated. Timings are local observations, not a calibrated benchmark.

The focused kernel handoff with the candidate enabled passes 105 tests / 747
assertions, including the existing kernel-soundness regressions. The four new
focused tests cover proof admission/rejection, cache isolation after an abandoned
probe, resource-abort propagation, and transparency/allow-list copying.

## Reproduce the Ansatz handoff

Compile Java first, then start a fresh JVM; a running REPL retains previously
loaded Java classes even if their class files are rebuilt.

```sh
clojure -T:build javac
clojure -J-Xmx1536m -J-Dansatz.kernel.experiment.congruence=true -M \
  experiments/kernel-111/replay.clj /path/to/foundation-selected.ndjson
clojure -J-Xmx1g -J-Dansatz.kernel.experiment.congruence=true -M:test \
  -n ansatz.kernel.projection-congruence-test -n ansatz.kernel-soundness-test
```

The JVM property defaults to false. The configurable probe budget is clamped to
0–4,096; a zero budget provides a fallback control. Default-disabled runs retain
the original conversion order.

## Init-only native model

`NativeModel.lean` builds the same synthetic theorem as raw kernel expressions;
its elaborator cannot normalize away the arithmetic index difference. It needs
only the pinned Lean installation and a tiny heartbeat-reset FFI helper:

```sh
task_lean_root=/path/to/lean-4.33.1
mkdir -p /tmp/ansatz111-model
"$task_lean_root/bin/lean" -c /tmp/ansatz111-model/NativeModel.c \
  experiments/kernel-111/NativeModel.lean
clang++ -std=c++17 -O2 -I "$task_lean_root/include" \
  -c experiments/kernel-111/native-budget.cpp -o /tmp/ansatz111-model/budget.o
"$task_lean_root/bin/leanc" -O2 -o /tmp/ansatz111-model/native-model \
  /tmp/ansatz111-model/NativeModel.c /tmp/ansatz111-model/budget.o
LEAN_SYSROOT="$task_lean_root" LEAN_NUM_THREADS=1 /tmp/ansatz111-model/native-model 4
LEAN_SYSROOT="$task_lean_root" LEAN_NUM_THREADS=1 /tmp/ansatz111-model/native-model 24
```

The small control checks. With the driver's 100,000 kernel-check budget, the
large control reports deterministic timeout and exits 2. Other kernel errors exit
1; success exits 0. This demonstrates the projection-normalization problem, not
the exact #14806 version boundary established by the Foundation controls.
