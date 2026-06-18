#!/usr/bin/env bash
# Regenerate the BUNDLED Init metadata corpora shipped in the jar (POINTERS into the store, NOT in
# the kernel export — lean4export emits only types + values):
#   resources/ansatz/init-attrs.ndjson.gz     (Lean's @[simp]/@[csimp]/@[extern]/@[implemented_by])
#   resources/ansatz/init-matchers.ndjson.gz  (Lean's Match.MatcherInfo — for the `split` tactic)
#
# Both are dumped from full `Init` (scripts/dump_attrs.lean / dump_matchers.lean) and are intersected
# with the loaded store's constants on import (ansatz.attrs/import-attrs, ansatz.matchers/
# import-matchers) — so a stale name simply skips and drift can only ever cost performance/
# completeness, never soundness. The one drift vector worth closing: regenerating the bundled Init
# STORE export from a new toolchain WITHOUT regenerating these. Run THIS script from the SAME
# ../lean4export checkout that produced the bundled store, every time you regenerate
# resources/ansatz/init-medium.ndjson.gz, so the three stay co-generated.
set -euo pipefail

PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
PARENT_DIR="$(dirname "$PROJECT_DIR")"
LEAN4EXPORT="$PARENT_DIR/lean4export"
OUT="$PROJECT_DIR/resources/ansatz/init-attrs.ndjson.gz"
OUT_MATCHERS="$PROJECT_DIR/resources/ansatz/init-matchers.ndjson.gz"

if [ ! -d "$LEAN4EXPORT" ]; then
    echo "ERROR: $LEAN4EXPORT not found. This must be the SAME lean4export checkout that produced" >&2
    echo "       the bundled Init store (resources/ansatz/init-medium.ndjson.gz)." >&2
    exit 1
fi

TC="$(cat "$LEAN4EXPORT/lean-toolchain" 2>/dev/null || echo '?')"
echo ">>> Dumping Init @[simp]/@[csimp]/@[extern] from $LEAN4EXPORT (toolchain $TC)"
cd "$LEAN4EXPORT"
lake env lean --run "$PROJECT_DIR/scripts/dump_attrs.lean" Init | gzip -c > "$OUT"
echo "    Wrote $OUT ($(zcat "$OUT" | wc -l) lines, toolchain $TC)"
echo ""
echo ">>> Dumping Init Match.MatcherInfo from $LEAN4EXPORT (toolchain $TC)"
lake env lean --run "$PROJECT_DIR/scripts/dump_matchers.lean" Init | gzip -c > "$OUT_MATCHERS"
echo "    Wrote $OUT_MATCHERS ($(zcat "$OUT_MATCHERS" | wc -l) matchers, toolchain $TC)"
echo ""
echo ">>> REMINDER: the bundled store (resources/ansatz/init-medium.ndjson.gz) must come from this"
echo "    SAME toolchain ($TC). If you just bumped the toolchain, regenerate the store too."
