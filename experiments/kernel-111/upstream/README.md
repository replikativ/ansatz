# Official Lean kernel performance reproducer

`Regression.lean` is standalone: its declarations require only Init, and it
imports Lean for the expression/environment API. It links no tracing code, FFI
helper, replacement kernel object, Ansatz implementation, or third-party library.

Run the exact packaged source with an unpacked official SDK:

```sh
./reproduce.sh /absolute/path/to/lean-4.32.1-linux 24
./reproduce.sh /absolute/path/to/lean-4.33.1-linux 24
./reproduce.sh /absolute/path/to/lean-4.35.0-linux 24
./reproduce.sh /absolute/path/to/lean-4.37.0-nightly-2026-10-27-linux 24
```

The first exits 0; the others exit 2 with `(kernel) deterministic timeout`.
Use `4` instead of `24` for a control that checks on every tested release.
The script adjusts only `addDeclCore`'s extra `maxRecDepth` parameter for 4.32.1.
It compiles with the selected SDK and runs a fresh native process. Running the
source through `lean --run` is not equivalent: its kernel heartbeat counter has
already accumulated work while compiling the source.

The 100,000 kernel-heartbeat limit is cumulative in the fresh process, including
the small preceding iterator declaration check. `IO.setNumHeartbeats` resets
allocation accounting only. Timings measure the target kernel result, forced
before reading the end clock. They exclude imports and iterator admission.

| Official SDK | n=24 outcome | Target allocation heartbeats |
| --- | --- | --- |
| 4.32.1 | checked, <1 ms | 448 |
| 4.33.1 | deterministic timeout, 107 ms | 51,090 |
| 4.35.0 | deterministic timeout, 117 ms | 51,090 |
| 4.37.0-nightly-2026-10-27 | deterministic timeout, 116 ms | 51,076 |

The small `n=4` control checks on every version. Timing values are local
observations; the outcome and allocation counts are more useful comparisons.
The same version contrast occurs on the original Foundation proof after a fully
checked prefix. Three repeated Foundation runs give stable outcomes/counts.

The iterator doubles composition of an identity function. The theorem is valid:
`Nat.add n 0` reduces to `n`, and the extra lambda application beta-reduces away.
The proof's inferred first binder has type `Fin n`, whereas the expected binder
has type `Fin (n + 0)`. Checking those domains supplies an equality before the
computed-projection comparison. The beta redex then triggers the old post-whnf
recursive equivalence lookup. This explains why the original simpler model in
`../NativeModel.lean`, without this context, times out on both old and new Lean.
It must not be presented as evidence of a version regression.

The contrast is consistent with loss of the old equivalence manager's recursive
cache-assisted congruence at Lean #14806. This is a performance report, not a
soundness claim or a proposal to restore the old unsound cache. The earlier
controlled reversal remains a separate, known-unsound diagnostic experiment.

`official-releases.json` records release download URLs and GitHub-published
SHA-256 digests. All four downloaded archives match those digests.
`official-runs.txt` records the native results, full-proof controls, and repeat
runs. `binary-provenance.json` confirms that the installed 4.32.1/4.33.1 Lean and
leanc executables, static kernel/Lean libraries, shared Lean library, and
Init.olean match the official archives byte for byte. All reproduction runs in
this directory used the freshly extracted official SDKs anyway.

A separate review agent audited the checked-prefix driver, expression indices,
proof validity, native compilation, and cumulative-budget accounting, and
approved the standalone reproducer for publication. The experimental Ansatz
kernel change remains disabled by default in draft PR #278.
