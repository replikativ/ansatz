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

Use the PSS-backed imported store for the authoritative full-corpus check:

```bash
clojure -M -e '
(require (quote [ansatz.export.storage :as s]))
(let [store (s/open-store "/var/tmp/ansatz-mathlib-new")]
  (try
    (prn (s/verify-from-store! store "mathlib"
                               :verbose? true
                               :timeout-ms 300000))
    (finally
      (s/close-store store))))
'
```

The store verifier defaults to 100M fuel per declaration. This is intentional:
Lean 4 itself has no fuel limit, and full Mathlib has legitimate declarations
above the interactive 20M fuel budget. The observed example on this branch was
`Polynomial.taylorLinearEquiv_symm`, which used about 25.4M fuel.

If a run stops after a known-good prefix, use `prepare-verify`, `skip-to!`, and
`verify-batch!` to resume. A resumed suffix validates the remaining declarations
against the staged environment, but record that the result was composed from a
prefix and suffix rather than one uninterrupted process.

Current full-corpus coverage from `/var/tmp/ansatz-mathlib-new`, branch
`mathlib`, was:

```clojure
{:total 648612
 :axiom 7
 :def 169615
 :thm 453415
 :opaque 3071
 :quot 4
 :induct 6589
 :ctor 9204
 :recursor 6707
 :nested-inductive-heads 55}
```

That run covered all imported declaration tags through the PSS staged verifier.
FlatStore has targeted tests, but full Mathlib-scale FlatStore verification is
not yet part of the normal validation gate.

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
