# CIC-CLJ — CIC Type Checker for Lean 4 Exports

## Build

Java kernel (required after changing `.java` files):
```bash
clj -T:build javac
```

Use system OpenJDK:
```bash
PATH=/usr/lib/jvm/java-25-openjdk-amd64/bin:$PATH
```

## Quick Tests

- `init-medium.ndjson` — 2997 declarations, ~1.5s. Fast smoke test.
- `init.ndjson` — 54335 declarations, ~50s. Full Init library.

Run from REPL:
```clojure
(require '[cic.export.storage :as s] :reload)
(def sm (s/import-ndjson-to-store "/var/tmp/cic-lmdb-test" "path/to/init-medium.ndjson" "test"))
(def ctx (s/prepare-verify sm "test"))
(s/verify-batch! ctx 3000 :verbose? true)
;; => should show 2997/2997, 0 errors
```

## REPL Workflow (Mathlib)

The full Mathlib store lives in `/var/tmp/cic-lmdb-mathlib` (648,612 declarations).

### Setup
```clojure
(require '[cic.export.storage :as s] :reload)
(def sm (s/open-store "/var/tmp/cic-lmdb-mathlib"))
(def ctx (s/prepare-verify sm "mathlib"))
```

### Navigation — skip is instant
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
(let [tc (cic.kernel.TypeChecker. (:env ctx))]
  (set! (.tracing tc) true)
  (set! (.traceLimit tc) 500))
```

## Lean 4 Kernel Tracing

The lean4 repo at `../lean4` has kernel tracing built in. Enable it with:
```bash
LEAN_KERNEL_TRACE=/tmp/lean-trace.ndjson lean4 ...
```
This outputs NDJSON lines with `{s, d, l, r, res, by}` (sequence, depth, lhs fingerprint, rhs fingerprint, result, resolved_by). Our Java TypeChecker emits the same format via `checkConstantTraced` / `setTraceWriter`. Use this to diff traces between Lean and our checker when debugging isDefEq divergences.

To trace a specific declaration in our checker:
```clojure
;; Use checkConstantTraced directly with a FileWriter
(import '[cic.kernel TypeChecker])
(let [w (java.io.FileWriter. "/tmp/cic-trace.ndjson")]
  (TypeChecker/checkConstantTraced (:env ctx) ci fuel w)
  (.close w))
```

## Key Design Decisions

- **Identity-based caches**: All caches (whnf, infer, failure, equiv) use `IdentityHashMap` after `shareCommon()`. Only `resultIntern` in Reducer uses structural `HashMap` (deduplication of new reduction results).
- **Default fuel**: 20M steps per declaration. Enough for all known mathlib proofs (~6M heaviest).
- **PSS storage**: Persistent sorted sets with LMDB backend. Branching is O(1).

## Important Workflow Rules

- **Never reprocess all 648k declarations to test a fix.** Jump to the failing declaration directly with `skip-to!` or `verify-by-name!`.
- **Full verification only as final validation** after individual fixes are confirmed.
- Use `:reload` when requiring namespaces to pick up code changes.
