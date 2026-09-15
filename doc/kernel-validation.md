# Kernel Validation

This document records the validation workflow for the Ansatz kernel. The goal is
to keep three checks separate:

1. Unit and integration tests for local regressions.
2. Trace comparison against the instrumented `../lean4` kernel for reduction
   order and definitional-equality behavior.
3. Full imported-store verification for semantic coverage over Mathlib.

## Standard Checks

Run these before opening a kernel PR:

```bash
clojure -T:build javac
clojure -M:test
```

The standard suite includes targeted checks for:

- `TypeChecker.checkConstant` on ordinary declarations.
- `TypeChecker.checkInductiveBundle` as the only inductive admission path.
- Staged imported-store visibility through `prepare-verify`.
- FlatStore verification through `prepare-verify-flat`.
- Quotient enablement in FlatStore-backed verification.
- Trace and phased-trace declaration checking entry points.
- Kernel trace comparison and curation utilities.

## Full Mathlib Verification

Use the PSS-backed imported store for the authoritative full-corpus check. The
runner verifies the store with one JVM per slice and is resumable:

```bash
./scripts/verify-mathlib.sh            # ~/.local/share/ansatz/stores/mathlib, 4 workers x 3 GB
./scripts/verify-mathlib.sh retry      # re-check what the run recorded as failures
```

Slice `i` of `WORKERS` runs `verify-corpus! :slice i` in its own process. A
slice admits the declarations before its start the way `skip-to!` does, so every
declaration is checked by exactly one worker against declarations that are
themselves checked; completing all slices gives the sequential run's guarantee.
Each slice checkpoints to `<store>/verify-<branch>-s<i>.edn` every 500
declarations, so a killed run continues where each slice stopped. A failed
declaration is recorded and then admitted for what follows (one failure instead
of a cascade of "unknown constant"), and a declaration that exhausts its heap
costs only its own worker. `reverify-errors!` (the `retry` mode) re-checks the
recorded entries one at a time at 10x fuel with a 10-minute CPU-time budget —
constructors and recursors through their inductive's bundle — and rewrites the
checkpoints to what still fails, logging each verdict to
`verify-<branch>-retry.log`.

The per-declaration timeout is CPU time (a paused or swapped process does not
time out), and the corpus default fuel is 100M per declaration: Lean 4 has no
fuel limit, and full Mathlib has legitimate declarations above the interactive
20M budget (`Polynomial.taylorLinearEquiv_symm` used about 25.4M).

A "timeout" or fuel exhaustion in this run is a kernel-completeness symptom
first and a performance one second: on the v4.33.1 store every root failure of
the first pass came from one deviation from the reference kernel (theorems were
not delta-unfolded, see `kernel_soundness_test`). Diagnose with
`verify-by-name!` and `TypeChecker` tracing before raising fuel.

Current full-corpus coverage — Mathlib `v4.33.1`, branch `mathlib`, store
format 1 — was:

```clojure
{:total 707508          ; verified 707507, recorded 1
 :axiom 7
 :def 176986
 :thm 504824
 :opaque 2587
 :quot 4
 :induct 6753
 :ctor 9482
 :recursor 6865}
```

Run of 2026-09-15 (branch `mathlib-4.33`): the first pass with four 3 GB workers
verified 705,380 declarations and recorded 2,128 — all but one of them shadows
of the theorem-unfolding fix landed mid-run — and the retry pass cleared 2,127
of those in about three minutes of check time. The one declaration not verified
is `localCohomology.diagramComp`, which exhausts its 600 s budget (a known
performance regression of the pair-based defeq cache, not a kernel rejection;
the pre-#84 union-find checked it in 1.6 s and Lean checks it instantly). The
checkpoints (`verify-mathlib-s0..3.edn`, `verify-mathlib.edn`) record exactly
this: 707,507 ok, 1 error.

## FlatStore Status

FlatStore is a performance-oriented mmap store path intended to reduce imported
kernel lookup and materialization overhead. It is not a second kernel: FlatStore
verification builds the same staged `Env` shape and calls the same
`verify-one!`, `TypeChecker.checkConstantFuel`, and
`TypeChecker.checkInductiveBundle` admission paths as PSS-backed verification.

Current FlatStore coverage is targeted:

- Import and verify the `Nat.add_succ` fixture through `prepare-verify-flat`.
- Check staged visibility before and after FlatStore admission.
- Check quotient enablement with a minimal FlatStore `Quot` fixture.

Full Mathlib-scale FlatStore verification is not yet part of the normal
validation gate. Until that is run and kept stable, the PSS-backed full Mathlib
verification remains the authoritative full-corpus kernel check.

## Trace Comparison

Trace comparison is the best tool when a declaration times out, exhausts fuel,
or looks suspiciously slower than Lean. It compares the Ansatz kernel trace with
the patched Lean 4 trace in `../lean4`.

Small Lean/init probe set:

```bash
clojure -M -m ansatz.tools.kernel-trace trace-batch-summary \
  /var/tmp/ansatz-mathlib-new mathlib ../lean4 \
  resources/kernel-trace-lean4-init.tsv \
  /tmp/ansatz-kernel-trace-init \
  100000000
```

Mathlib smoke and expanded probe sets:

```bash
clojure -M -m ansatz.tools.kernel-trace trace-batch-summary \
  /var/tmp/ansatz-mathlib-new mathlib ../mathlib4 \
  resources/kernel-trace-mathlib-smoke.tsv \
  /tmp/ansatz-kernel-trace-smoke \
  100000000 lake

clojure -M -m ansatz.tools.kernel-trace trace-batch-summary \
  /var/tmp/ansatz-mathlib-new mathlib ../mathlib4 \
  resources/kernel-trace-mathlib-expanded.tsv \
  /tmp/ansatz-kernel-trace-expanded \
  100000000 lake
```

Use `curate-batch` or `curate-batch-grouped` before promoting new trace targets.
Ambiguous Lean traces and metadata-only mismatches should be quarantined instead
of being treated as kernel semantic matches.

## Interpreting Failures

- A kernel `:error` is a semantic failure until proven otherwise; compare with
  `../lean4` and inspect the declaration.
- `:fuel-exceeded` can be a real divergence, but first measure the declaration
  with `TypeChecker/checkConstantFuel`. If it succeeds just above the current
  budget, raise the verifier fuel for that run and record the outlier.
- Large trace-length differences are not automatically unsound, but they make
  regressions harder to inspect. Prefer reducing semantic mismatches first,
  then tightening trace length/order where it does not distort the kernel.
- Full Mathlib verification is the final gate; trace probes are a cheaper way
  to catch reduction-order regressions before paying for that run.
