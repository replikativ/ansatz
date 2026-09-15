#!/bin/bash
# Full kernel verification of an imported store — resumable, one JVM per slice.
#
#   ./scripts/verify-mathlib.sh [STORE_DIR]          verify (resumes from the per-slice checkpoints)
#   ./scripts/verify-mathlib.sh retry [STORE_DIR]    re-check what the run recorded as failures
#
# Each slice i of WORKERS runs `verify-corpus! :slice i` in its own JVM and checkpoints to
# <store>/verify-<branch>-s<i>.edn every 500 declarations, so a killed run continues where each
# slice stopped, and a declaration that exhausts its heap costs only its own worker (recorded as
# a failure, not fatal). `retry` runs `reverify-errors!` over the recorded entries at 10x fuel /
# a 10 min CPU-time budget each and rewrites the checkpoints to what still fails. The retry
# runs one JVM with RETRY_HEAP (8g): the two heaviest Mathlib declarations
# (localCohomology.diagramComp, AlgebraicGeometry.Proj.awayι_comp_map) need 5-6 GB of live
# heap — Lean's own kernel peaks at 3.5 GB RSS on the first — and verify in under a minute.
#
# Environment: WORKERS (4), HEAP per worker (3g), RETRY_HEAP (8g), BRANCH (mathlib), ANSATZ_STORE_DIR.
# Logs: <store>/verify-<branch>-w<i>.log and verify-<branch>-retry.log; stdout of each JVM in
# <store>/verify-<branch>-s<i>.out.
set -euo pipefail
cd "$(dirname "$0")/.."

MODE=verify
if [ "${1:-}" = "retry" ]; then MODE=retry; shift; fi
DEFAULT_ROOT="${ANSATZ_STORE_DIR:-${XDG_DATA_HOME:-$HOME/.local/share}/ansatz/stores}"
STORE_DIR="${1:-$DEFAULT_ROOT/mathlib}"
WORKERS="${WORKERS:-4}"; HEAP="${HEAP:-3g}"; RETRY_HEAP="${RETRY_HEAP:-8g}"; BRANCH="${BRANCH:-mathlib}"
[ -d "$STORE_DIR/blobs" ] || { echo "no store at $STORE_DIR" >&2; exit 1; }

JVM=(clj -J-Xmx"$HEAP" -J-XX:+UseParallelGC -M -e)
open="(require '[ansatz.export.storage :as s]) (let [sm (s/open-store \"$STORE_DIR\")] (try"
close="(finally (s/close-store sm)))) (shutdown-agents)"

if [ "$MODE" = retry ]; then
  JVM=(clj -J-Xmx"$RETRY_HEAP" -J-XX:+UseParallelGC -M -e)
  "${JVM[@]}" "$open (let [r (s/reverify-errors! sm \"$BRANCH\" :fuel 1000000000 :timeout-ms 600000)] (println \"RETRY DONE fixed\" (count (:fixed r)) \"still-failing\" (count (:still-failing r))) (doseq [e (:still-failing r)] (println \"  \" (:name e) \"--\" (:error e)))) $close" \
    2>&1 | tee "$STORE_DIR/verify-$BRANCH-retry.out"
  exit 0
fi

echo "verifying $STORE_DIR branch $BRANCH with $WORKERS workers x $HEAP"
pids=()
for ((i=0; i<WORKERS; i++)); do
  "${JVM[@]}" "$open (let [r (s/verify-corpus! sm \"$BRANCH\" :workers $WORKERS :slice $i :checkpoint-every 500 :timeout-ms 300000)] (println \"SLICE $i DONE\" (pr-str (select-keys r [:ok :errors :done?])))) $close" \
    > "$STORE_DIR/verify-$BRANCH-s$i.out" 2>&1 &
  pids+=($!)
done
status=0
for p in "${pids[@]}"; do wait "$p" || status=1; done
grep -h "SLICE" "$STORE_DIR"/verify-"$BRANCH"-s*.out || true
echo "next: ./scripts/verify-mathlib.sh retry $STORE_DIR   # re-check recorded failures at high fuel"
exit $status
