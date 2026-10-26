# Unchanged program runtime corpus

These are **native frontend exports for raw runtime testing**. They do not test
hosted file loading, source elaboration on the JVM, Ansatz kernel admission,
whole Mathlib compatibility, or sampler execution.

`sources.json` pins original source bytes and revisions. The `.lean` files are
exact Git blobs, without harness declarations appended. `rbmap.lean` is Lean's
existing red/black map benchmark; `CompilerIR.lean` is Mcmc's backend-neutral
sampler DSL data model. Constructing that DSL does not execute its represented
sampler. The original copyright notice in rbmap is preserved.

The producer is Lean 4.33.1 at
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The capture used the existing
`lean/Export.lean` executable, SHA-256
`0b0344058631b8c3dc18a8a1a600f8100611eaf49c3b4ee5ad18a121651e736e`, with an
explicit matching sysroot and a clean child environment. Both source-local
initialization plans are empty. The JSONL manifests retain original producer
metadata; each selected declaration line is copied verbatim from the capture.

- `rbmap.jsonl`: 15 demand-closed declarations rooted at `mkMap`,
  `fold._redArg`, and `main._closed_0`. Its five externs are the existing Nat
  subtraction, equality, modulo, addition, and less-than operations. The original
  `main` callback closure counts true values. Original main IO/string code is
  excluded from this runtime closure; no whole-main JVM execution is claimed.
- `compiler-ir.jsonl`: 81 demand-closed declarations, no externs. The roots are
  `categoricalProgram`, `metropolisHastingsProgram`, `twoStateTarget`, and
  `twoStateProposal` in `Mcmc.Executable.Finite.CompilerIR`.

From `experiments/lean-ir`, provide existing producer/sysroot paths explicitly:

```sh
python3 scripts/capture-unchanged-program.py \
  --exporter "$ANSATZ_IR_EXPORTER" --sysroot "$LEAN_SYSROOT" \
  --source test/fixtures/unchanged-programs/rbmap.lean \
  --output target/unchanged-programs/rbmap --module UnchangedRbmap \
  mkMap fold main
python3 scripts/select-unchanged-closure.py \
  target/unchanged-programs/rbmap/ir.jsonl \
  test/fixtures/unchanged-programs/rbmap.jsonl \
  mkMap fold._redArg main._closed_0
```

The capture refuses to overwrite its output, verifies the producer pin, enforces
1800 MiB process-group RSS and 120 seconds, and preserves stdout/stderr and a
receipt. Coordinate the native slot with other memory-heavy work. The selected
closure utility refuses unresolved declarations; runtime linking additionally
derives static dependencies from admitted bodies rather than trusting metadata.

`research/unchanged-program-benchmark.clj` is an external host harness. Load it
into the existing resident REPL without reloading runtime/compiler namespaces.
Its `rbmap` function builds the original map, then executes the original fold
with the original main callback; complete Worlds must match across reference,
mutable, and lazy JVM routes. It checks the numeric result for every input.
`compiler-ir` compares complete Worlds for the four constant-constructor roots;
it does not yet supply an independent native value oracle.

Measurements include current-thread CPU/allocation, wall time, global GC count,
cumulative guest World steps/allocations and retained heap shape. The rbmap
World counters include the original callback initialization, which occurs outside
the timed execution. `next-id` is a cumulative allocation identifier, not a
measurement of maximum simultaneous live objects. The retained tree at fold
entry is recorded separately from the heap remaining after fold. Fresh World construction is
outside measured execution; thaw/run/freeze and the intermediate fold start are
inside it. The JVM summary reports actual compiled/cache/dispatch counts for the generic
lazy JVM route; this harness requests no scalar-region specialization.
Preparation and the first n=11 run are recorded separately. Two n=11 warmups do
not establish steady state. These numbers cannot be read as compiled-native
versus JVM performance comparisons.

Native capture verification on 2026-10-26: rbmap exported 80 declarations before
selection, no missing declarations, exit 0, 5.10 s, peak group RSS 704,090,112
bytes; CompilerIR exported 81 declarations, no missing declarations, exit 0,
2.22 s, peak group RSS 713,932,800 bytes. The exact unchanged rbmap source with
pinned `lean --run … 100` returned exit 0 and stdout `10\n` (0.51 s,
280,227,840 bytes peak group RSS). This native command uses Lean's evaluation
route, not a separately compiled C executable.

Resident runtime verification on 2026-10-26 used the existing 192 MiB heap JVM,
without loading a full Init environment or starting another JVM. All complete
World comparisons passed for rbmap inputs 0, 1, 11, 100, and 1000, three trials
per backend. Input 1000 returned 100. Its cumulative World counters were 483,997
steps, 14,896 constructor allocations, 32,752 field stores, and maximum 18
frames. The tree occupied 1001 retained heap nodes at fold entry (including the
callback); the final heap retained one callback node. The generic lazy JVM
compiled 35 blocks.

Input 1000 medians across those three trials:

| Backend | Thread CPU | Wall | Thread allocation |
| --- | ---: | ---: | ---: |
| Reference | 778.9 ms | 855.8 ms | 933,411,976 B |
| Mutable | 304.5 ms | 334.7 ms | 238,378,792 B |
| Lazy JVM | 265.8 ms | 297.9 ms | 163,432,144 B |

These are bounded resident samples, not steady-state performance estimates.
CompilerIR's four roots also passed complete World parity for two trials per
backend. The JVM compiled 292 blocks with 133 cache hits across those calls.
The second MH constructor call used 19.45 ms thread CPU and allocated 3,263,296
host bytes; the returned graph had 43 guest allocations and maximum 33 frames.
This is constructor-data execution, with no independent native value oracle.

The machine-readable receipt and exact samples are in
`measurements/unchanged-program-resident-validation.json`,
`measurements/unchanged-rbmap-2026-10-26.edn`, and
`measurements/unchanged-compiler-ir-2026-10-26.edn` (paths relative to
`experiments/lean-ir`). The receipt pins the exact measured harness SHA-256.
Python syntax checks, source SHA-256 audits, dependency selection audits, and
staged whitespace checks passed. The full Clojure suite, whole Init restoration,
and a native C executable build were not run; the resident-only constraint
was preserved.
