# Ansatz — Verified Clojure via Lean 4 Mathlib

## Build

Java kernel (required after changing `.java` files):
```bash
clj -T:build javac
```

## Quick Tests

- `init-medium.ndjson` — 2997 declarations, ~1.5s. Fast smoke test.
- `init.ndjson` — 54335 declarations, ~50s. Full Init library.

Run tests:
```bash
clj -M:test
```

## Setup Mathlib Store

Run the setup script (clones lean4export + mathlib4, exports, imports):
```bash
./scripts/setup-mathlib.sh
```

Or manually:
```bash
./scripts/setup-mathlib.sh /var/tmp/ansatz-mathlib
```

## REPL Workflow (Mathlib)

The full Mathlib store lives in `/var/tmp/ansatz-mathlib` (648,612 declarations).

### Setup
```clojure
(require '[ansatz.core :as a] :reload)
(a/init! "/var/tmp/ansatz-mathlib" "mathlib")
```

### Proving theorems
```clojure
;; Define a verified function
(a/defn gd-step [x :- Real, grad :- Real, eta :- Real] Real
  (sub Real x (mul Real eta grad)))

;; Prove convergence
(a/theorem gd-rate [κ :- Real, ε₀ :- Real, n :- Nat,
                     hκ₀ :- (<= Real 0 κ), hκ₁ :- (<= Real κ 1), hε₀ :- (<= Real 0 ε₀)]
  (<= Real (mul Real (pow Real κ n) ε₀) ε₀)
  (apply mul_le_of_le_one_left) (assumption)
  (apply pow_le_one₀) (all_goals (assumption)))
```

### Navigation — skip is instant (for verification debugging)
PSS external lookup loads declarations on demand, so skipping doesn't reprocess anything:
```clojure
(s/skip! ctx 300000)        ;; advance by 300k
(s/skip-to! ctx 313165)     ;; jump directly to index
(s/find-decl ctx "sizeOf")  ;; find indices by name substring
```

### Targeted verification
```clojure
(s/verify-one! ctx)                              ;; verify next declaration
(s/verify-one! ctx :fuel 50000000)               ;; with custom fuel (default 20M)
(s/verify-by-name! ctx "Nat.add_comm")           ;; find + verify by exact name
(s/verify-batch! ctx 100 :verbose? true)         ;; verify next 100
(s/verify-batch! ctx 100 :stop-on-error? false)  ;; don't stop on errors
```

### Inspecting results
`verify-one!` returns a map with `:status`, `:name`, `:fuel-used`, `:elapsed-ms`, `:stats`, `:trace`, `:error`.

### Tracing (for debugging isDefEq / whnf)
```clojure
;; Enable tracing on the TypeChecker before verify-one!
(let [tc (ansatz.kernel.TypeChecker. (:env ctx))]
  (set! (.tracing tc) true)
  (set! (.traceLimit tc) 500))
```

## Lean 4 Kernel Tracing

The lean4 repo at `../lean4` has kernel tracing — this was added by us (commit `55f80e10`, not in upstream Lean 4). Enable it with:
```bash
LEAN_KERNEL_TRACE=/tmp/lean-trace.ndjson lean4 ...
```
This outputs NDJSON lines with `{s, d, l, r, res, by}` (sequence, depth, lhs fingerprint, rhs fingerprint, result, resolved_by). Our Java TypeChecker emits the same format via `checkConstantTraced` / `setTraceWriter`. Use this to diff traces between Lean and our checker when debugging isDefEq divergences.

To trace a specific declaration in our checker:
```clojure
;; Use checkConstantTraced directly with a FileWriter
(import '[ansatz.kernel TypeChecker])
(let [w (java.io.FileWriter. "/tmp/ansatz-trace.ndjson")]
  (TypeChecker/checkConstantTraced (:env ctx) ci fuel w)
  (.close w))
```

## Lean 4 Reference

The Lean 4 source at `../lean4` is our reference implementation. When porting infrastructure (simp, tactics, type checking), always study the Lean 4 source first and implement faithfully. Key files:

- `src/Lean/Meta/Tactic/Simp/Main.lean` — simp core (simpLoop, simpStep)
- `src/Lean/Meta/Tactic/Simp/Rewrite.lean` — rewrite, discharge, dischargeDefault?
- `src/Lean/Meta/Tactic/Simp/SimpAll.lean` — simp_all loop
- `src/Lean/Meta/Tactic/Simp/Types.lean` — CongrArgKind, tryAutoCongrTheorem?
- `src/Lean/Meta/CongrTheorems.lean` — getCongrSimpKinds, fixKindsForDependencies
- `src/Lean/Meta/Tactic/Apply.lean` — apply tactic with isDefEq matching
- `src/Lean/Meta/FunInfo.lean` — FunInfo, hasFwdDeps, backDeps

### Ported infrastructure (validated)
- CongrArgKind system (get-fun-info, get-congr-simp-kinds)
- dsimp-expr (separate traversal, structural reductions only)
- Bool.rec simpMatch with constant-motive override
- Rewrite candidate priority sort (rewriteUsingIndex?)
- Disc tree star-skip for nested arity (consume/getStarResult)
- Bool.rec→Bool.and context-sensitive fold
- Prop guards (extract-from-conclusion, try-simp-using-decide)
- simp_all Phase 1+2 with Eq.mp transport
- Discharger with rfl case, omega fallback, fresh cache
- Comprehensive hypothesis preprocessing (And-split, implications)

### RESOLVED: apply tactic def-eq matching
Fixed via WHNF extraction + isDefEq for indexed family constructors.
The grind tactic's IH application strategy also handles this case.

### RESOLVED: Env is now immutable
Env uses Clojure's IPersistentMap for locals (structural sharing).
addConstant() returns a NEW Env. fork() is a no-op. Thread-safe
for concurrent reads via ConcurrentHashMap sharedCache.

**Known issue:** The global `ansatz-env` atom uses `reset!` in
`defn`/`theorem`, which captures env early in a `let` and resets
later. Concurrent `defn` calls can lose additions (stale env race).
Single-threaded REPL use is safe. Fix: use `swap!` with
`env/add-constant` or add a mutex around definition boundaries.

## Development Guidelines

- **Take time to get things right.** Carefully validate each change against
  the Lean 4 source and the full test suite. Don't rush fixes that might
  introduce regressions.
- **Study `../lean4` before implementing.** The Lean 4 source is the
  authoritative reference. When unsure about behavior, read the actual code.
- **Run full test suite** (`clj -M:test -e :wip`) after every change.
  All non-WIP tests must pass. Currently 391 tests, 0 errors.
- **Use `*simp-trace*`** for debugging simp rewrite issues. Bind to an atom
  to collect trace entries showing where corruption or unexpected rewrites occur.
- **Test isolation**: Tests use `:once` fixture with shared env. Definitions
  accumulate across tests. Use `env/fork` + try/finally for tests that need
  clean state (see `test-isort-preservation` as the model).

## Key Design Decisions

- **Identity-based caches**: All caches (whnf, infer, failure, equiv) use `IdentityHashMap` after `shareCommon()`. Only `resultIntern` in Reducer uses structural `HashMap` (deduplication of new reduction results).
- **Default fuel**: 20M steps per declaration. Enough for all known mathlib proofs (~6M heaviest).
- **PSS storage**: Persistent sorted sets with LMDB backend. Branching is O(1).

## Important Workflow Rules

- **Never reprocess all 648k declarations to test a fix.** Jump to the failing declaration directly with `skip-to!` or `verify-by-name!`.
- **Full verification only as final validation** after individual fixes are confirmed.
- Use `:reload` when requiring namespaces to pick up code changes.
