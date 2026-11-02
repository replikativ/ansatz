### Description

A small valid declaration built from raw `Lean.Expr`s checks immediately with
official Lean 4.32.1 but exhausts a 100,000 cumulative kernel-heartbeat limit
with official 4.33.1, 4.35.0, and the latest available nightly,
4.37.0-nightly-2026-10-27.

The fixture needs only Init declarations. It imports Lean for the expression and
kernel-environment API. The executable is compiled using only the selected
official SDK; it contains no custom kernel object, tracing instrumentation, or
FFI helper. Fresh downloaded release archives were verified against the SHA-256
digests published on their GitHub release assets.

### Reproduction

Save the following as `Regression.lean`. The expressions are built explicitly
because ordinary source elaboration can simplify away the `n + 0` and beta-redex
shape that triggers the contrast.

```lean
import Lean
open Lean

-- Build raw kernel expressions so elaboration cannot normalize away 24 + 0.
-- The Fin binder comparison precedes the computed-projection comparison.
-- The beta redex exercises post-whnf comparison.
def projectionModel (n : Nat) : Declaration × Declaration := Id.run do
  let nat := mkConst ``Nat
  let u := Level.zero
  let fnType := mkForall `x .default nat nat
  let pairType := mkApp2 (mkConst ``Prod [u, u]) fnType nat
  let pair := fun f => mkApp4 (mkConst ``Prod.mk [u, u]) fnType nat f (mkNatLit 0)
  let first := fun p => mkProj ``Prod 0 p
  let base := pair (mkLambda `x .default nat (mkBVar 0))
  let previous := first (mkBVar 1)
  let step := mkLambda `k .default nat <| mkLambda `prev .default pairType <|
    pair (mkLambda `x .default nat (mkApp previous (mkApp previous (mkBVar 0))))
  let iterBody := fun k => mkApp4 (mkConst ``Nat.rec [Level.succ u])
    (mkLambda `_ .default nat pairType) base step k
  let iterator := Declaration.defnDecl {
    name := `ProjectionRegression.iterator
    levelParams := []
    type := mkForall `n .default nat pairType
    value := mkLambda `n .default nat (iterBody (mkBVar 0))
    hints := .regular 1
    safety := .safe
    all := [`ProjectionRegression.iterator]
  }
  let iter := fun k => mkApp (mkConst `ProjectionRegression.iterator) k
  let lhs := mkApp (first (iter (mkNatLit n))) (mkBVar 0)
  let rhs := mkApp (first (iter (mkApp2 (mkConst ``Nat.add) (mkNatLit n) (mkNatLit 0))))
    (mkBVar 0)
  let count := mkNatLit n
  let countPlusZero := mkApp2 (mkConst ``Nat.add) count (mkNatLit 0)
  let goal := mkApp3 (mkConst ``Eq [Level.succ u]) nat lhs rhs
  let betaLhs := mkApp (mkLambda `unused .default nat (lhs.liftLooseBVars 0 1)) (mkNatLit 0)
  let proof := mkApp2 (mkConst ``Eq.refl [Level.succ u]) nat betaLhs
  return (iterator, .thmDecl {
    name := `ProjectionRegression.projectionModel
    levelParams := []
    type := mkForall `a .default (mkApp (mkConst ``Fin) countPlusZero)
      (mkForall `x .default nat goal)
    value := mkLambda `a .default (mkApp (mkConst ``Fin) count)
      (mkLambda `x .default nat proof)
    all := [`ProjectionRegression.projectionModel]
  })

unsafe def main (args : List String) : IO UInt32 := do
  let some root ← IO.getEnv "LEAN_SYSROOT" | throw <| IO.userError "set LEAN_SYSROOT"
  initSearchPath root
  let n := args.head?.bind String.toNat? |>.getD 24
  withImportModules #[{module := `Init}] {} fun env => do
    let (iterator, thm) := projectionModel n
    let .ok kernelEnv := env.toKernelEnv.addDeclCore 0 0 iterator none
      | throw <| IO.userError "failed iterator declaration"
    -- Allocation heartbeats only. The kernel budget below is cumulative within
    -- this fresh native process, including the small iterator check above.
    IO.setNumHeartbeats 0
    let start ← IO.monoMsNow
    -- Force the kernel result before collecting the end time/allocation count.
    match kernelEnv.addDeclCore 100000 0 thm none with
    | .ok _ =>
      IO.println s!"checked n={n} elapsed_ms={(← IO.monoMsNow) - start} allocations={(← IO.getNumHeartbeats)}"
      return 0
    | .error ex =>
      IO.println s!"failed n={n} elapsed_ms={(← IO.monoMsNow) - start} allocations={(← IO.getNumHeartbeats)}"
      IO.println <| ← ex.toMessageData {} |>.toString
      return if let .deterministicTimeout := ex then 2 else 1
```

Using an unpacked official Lean 4.33.1 SDK:

```sh
task_lean_root=/absolute/path/to/lean-4.33.1-linux
"$task_lean_root/bin/lean" -c Regression.c Regression.lean
"$task_lean_root/bin/leanc" -O2 -o regression Regression.c
LEAN_SYSROOT="$task_lean_root" LEAN_NUM_THREADS=1 ./regression 4
LEAN_SYSROOT="$task_lean_root" LEAN_NUM_THREADS=1 ./regression 24
```

The `4` control exits 0. The `24` case exits 2 and reports
`(kernel) deterministic timeout`.

For 4.32.1, remove the extra `maxRecDepth` argument at the two `addDeclCore`
calls: `addDeclCore 0 0 iterator` becomes `addDeclCore 0 iterator`, and
`addDeclCore 100000 0 thm` becomes `addDeclCore 100000 thm`. Those are the only
source changes between versions. Both inputs then exit 0.

Please compile a native executable as above: `lean --run` would include the
source compilation's earlier work in the thread's kernel heartbeat counter.
`IO.setNumHeartbeats 0` resets allocation accounting, not the separate kernel
check counter. The 100,000 limit here is cumulative in the fresh executable,
including the small iterator declaration check before the theorem.

A [script automating the version adjustment and isolated build](https://github.com/replikativ/ansatz/blob/94bef94/experiments/kernel-111/upstream/reproduce.sh),
[official artifact metadata/checksums](https://github.com/replikativ/ansatz/blob/94bef94/experiments/kernel-111/upstream/official-releases.json),
and [recorded outcomes](https://github.com/replikativ/ansatz/blob/94bef94/experiments/kernel-111/upstream/official-runs.txt)
are available.

### Observations

Linux x86-64, official release builds. Times below measure only the target
kernel check, with its result forced before collecting the end clock. They
exclude import and iterator checking. Millisecond timing is coarse; the fixed
outcomes/allocation counts are the useful comparison.

| Official version | Commit | n=24 result | Target allocation heartbeats |
| --- | --- | --- | --- |
| 4.32.1 | `f054605aea4b` | checked, <1 ms | 448 |
| 4.33.1 | `819816b2e0a3` | deterministic timeout, 107 ms | 51,090 |
| 4.35.0 | `eb6cafb7290e` | deterministic timeout, 117 ms | 51,090 |
| 4.37.0-nightly-2026-10-27 | `67bc4fe8130f` | deterministic timeout, 116 ms | 51,076 |

The `n=4` control checks on all four versions.

### Shape and possible connection

The iterator doubles composition of an identity function at each step. The
proof's inferred first binder has type `Fin n`; the expected binder has type
`Fin (n + 0)`. Checking those domains establishes an equality before comparing
applications of computed projections. There is also a beta-redex around the
projection application on the proof side. The theorem is valid by reduction:
`Nat.add n 0` reduces to `n`, and the unused lambda application beta-reduces away.

The version contrast appears consistent with losing the old equivalence
manager's recursive cache-assisted congruence in #14806. This is a performance
report, not a soundness claim or a request to restore the old cache. A smaller
model without this binder-comparison/beta-redex context was slow on both old
and new releases, so that model is not the reproducer supplied here.

Related #14803 also concerns normalization before a cheaper equality check, but
its reported version range starts before #14806 and its fixture has a different
shape.

### Original context

Found while investigating [an independent checker OOM on a Foundation proof
export](https://github.com/replikativ/ansatz/issues/111). Replaying the same
4.32-produced proof through each official Lean kernel checks its entire dependency
prefix, then accepts this theorem with 4.32.1 and times out on 4.33.1, 4.35.0,
and the nightly. Three repeated 4.32.1/4.33.1 runs have identical respective
allocation counts. The standalone fixture above removes the Foundation/Mathlib
and exporter dependencies from that observation.

### Prerequisites

- [x] Searched existing issues; related #14803 noted above.
- [x] Standalone reproducible case with Init-only declaration dependencies.
- [x] Tested latest available nightly (nightly-2026-10-27).
