#!/usr/bin/env bash
# Setup Ansatz Mathlib store from scratch.
#
# Prerequisites:
#   - Lean 4 (elan): https://github.com/leanprover/elan
#   - Java 21+
#   - Clojure CLI 1.12+
#
# This script:
#   1. Clones lean4export and mathlib4 (if not present)
#   2. Builds lean4export
#   3. Exports Mathlib to NDJSON
#   4. Generates instances.tsv
#   5. Imports into Ansatz PSS filestore
#
# Usage:
#   ./scripts/setup-mathlib.sh [STORE_DIR]
#
# Default STORE_DIR: /var/tmp/ansatz-mathlib

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
STORE_DIR="${1:-/var/tmp/ansatz-mathlib}"
PARENT_DIR="$(dirname "$PROJECT_DIR")"

echo "=== Ansatz Mathlib Setup ==="
echo "Project:  $PROJECT_DIR"
echo "Store:    $STORE_DIR"
echo ""

# ============================================================
# Step 1: Clone dependencies (if not present)
# ============================================================

if [ ! -d "$PARENT_DIR/lean4export" ]; then
    echo ">>> Cloning lean4export..."
    git clone https://github.com/leanprover/lean4export.git "$PARENT_DIR/lean4export"
else
    echo ">>> lean4export already present at $PARENT_DIR/lean4export"
fi

if [ ! -d "$PARENT_DIR/mathlib4" ]; then
    echo ">>> Cloning mathlib4 (this may take a while)..."
    git clone https://github.com/leanprover-community/mathlib4.git "$PARENT_DIR/mathlib4"
else
    echo ">>> mathlib4 already present at $PARENT_DIR/mathlib4"
fi

# ============================================================
# Step 2: Build lean4export
# ============================================================

echo ""
echo ">>> Building lean4export..."
cd "$PARENT_DIR/lean4export"
lake build
echo "    Built: $(ls .lake/build/bin/lean4export 2>/dev/null && echo 'OK' || echo 'FAILED')"

# ============================================================
# Step 3: Export Mathlib to NDJSON
# ============================================================

NDJSON="$PROJECT_DIR/test-data/mathlib.ndjson"
if [ -f "$NDJSON" ]; then
    echo ""
    echo ">>> NDJSON already exists at $NDJSON ($(du -h "$NDJSON" | cut -f1))"
    echo "    Delete it to re-export."
else
    echo ""
    echo ">>> Exporting Mathlib to NDJSON (this takes ~5 minutes)..."
    mkdir -p "$PROJECT_DIR/test-data"
    .lake/build/bin/lean4export --mathlib > "$NDJSON"
    echo "    Exported: $(du -h "$NDJSON" | cut -f1)"
fi

# ============================================================
# Step 4: Generate instances.tsv
# ============================================================

INSTANCES_TSV="$PROJECT_DIR/resources/instances.tsv"
if [ -f "$INSTANCES_TSV" ]; then
    echo ""
    echo ">>> instances.tsv already exists ($(wc -l < "$INSTANCES_TSV") lines)"
    echo "    Delete it to regenerate."
else
    echo ""
    echo ">>> Generating instances.tsv from Mathlib..."
    cd "$PARENT_DIR/mathlib4"

    # Create temporary DumpInstances.lean if not present
    if [ ! -f "DumpInstances.lean" ]; then
        cat > DumpInstances.lean << 'LEAN'
import Mathlib

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (name, ci) in env.constants.map₁.toList do
    if (← Meta.isInstance name) then
      let mut ty := ci.type
      while ty.isForall do
        ty := ty.bindingBody!
      let head := ty.getAppFn
      if let .const className _ := head then
        lines := lines.push s!"{className}\t{name}\t100"
  IO.FS.writeFile "instances.tsv" (String.intercalate "\n" lines.toList)
  IO.eprintln s!"Wrote {lines.size} instances"
LEAN
    fi

    lake env lean DumpInstances.lean
    cp instances.tsv "$INSTANCES_TSV"
    echo "    Generated: $(wc -l < "$INSTANCES_TSV") instances"
fi

# ============================================================
# Step 5: Import into Ansatz store
# ============================================================

echo ""
echo ">>> Importing into Ansatz PSS filestore at $STORE_DIR..."
echo "    This takes ~15 minutes for full Mathlib."

cd "$PROJECT_DIR"

# Compile Java kernel first
clj -T:build javac 2>/dev/null || true

clj -M -e "
(require '[ansatz.export.storage :as s])
(println \"Opening store at $STORE_DIR ...\")
(def store (s/open-store \"$STORE_DIR\"))
(println \"Starting import...\")
(time (s/import-ndjson-streaming! store \"$NDJSON\" \"mathlib\" :verbose? true))
(println \"Done.\")
"

echo ""
echo "=== Setup Complete ==="
echo ""
echo "Store: $STORE_DIR ($(du -sh "$STORE_DIR" | cut -f1))"
echo ""
echo "To use in Clojure:"
echo "  (require '[ansatz.core :as a])"
echo "  (a/init! \"$STORE_DIR\" \"mathlib\")"
echo ""
