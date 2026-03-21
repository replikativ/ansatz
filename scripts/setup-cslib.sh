#!/usr/bin/env bash
# Setup Ansatz CSLib store from scratch.
#
# CSLib (github.com/leanprover/cslib) is the official Computer Science library
# for Lean 4 — verified algorithms, automata, lambda calculus, and more.
#
# Prerequisites:
#   - Lean 4 (elan): https://github.com/leanprover/elan
#   - Java 21+
#   - Clojure CLI 1.12+
#
# This script:
#   1. Clones cslib and lean4export (if not present)
#   2. Builds cslib (downloads mathlib dependency, ~1-2h first time)
#   3. Builds lean4export (matching cslib's Lean version)
#   4. Exports CSLib to NDJSON
#   5. Imports into Ansatz PSS filestore
#
# Usage:
#   ./scripts/setup-cslib.sh [STORE_DIR]
#
# Default STORE_DIR: /var/tmp/ansatz-cslib

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
STORE_DIR="${1:-/var/tmp/ansatz-cslib}"
PARENT_DIR="$(dirname "$PROJECT_DIR")"

echo "=== Ansatz CSLib Setup ==="
echo "Project:  $PROJECT_DIR"
echo "Store:    $STORE_DIR"
echo ""

# ============================================================
# Step 1: Clone dependencies (if not present)
# ============================================================

if [ ! -d "$PARENT_DIR/cslib" ]; then
    echo ">>> Cloning cslib..."
    git clone https://github.com/leanprover/cslib.git "$PARENT_DIR/cslib"
else
    echo ">>> cslib already present at $PARENT_DIR/cslib"
fi

if [ ! -d "$PARENT_DIR/lean4export" ]; then
    echo ">>> Cloning lean4export..."
    git clone https://github.com/leanprover/lean4export.git "$PARENT_DIR/lean4export"
else
    echo ">>> lean4export already present at $PARENT_DIR/lean4export"
fi

# ============================================================
# Step 2: Build cslib (fetches mathlib, builds everything)
# ============================================================

echo ""
echo ">>> Building cslib (downloads mathlib dependency, ~1-2h first time)..."
cd "$PARENT_DIR/cslib"
lake build
echo "    Build complete."

# ============================================================
# Step 3: Build lean4export (matching cslib's Lean version)
# ============================================================

echo ""
echo ">>> Building lean4export..."
cd "$PARENT_DIR/lean4export"

# Match lean4export's toolchain to cslib's
CSLIB_TOOLCHAIN=$(cat "$PARENT_DIR/cslib/lean-toolchain")
echo "$CSLIB_TOOLCHAIN" > lean-toolchain
lake build
echo "    Built lean4export for $CSLIB_TOOLCHAIN"

# ============================================================
# Step 4: Export CSLib to NDJSON
# ============================================================

NDJSON="$PROJECT_DIR/test-data/cslib.ndjson"
if [ -f "$NDJSON" ]; then
    echo ""
    echo ">>> NDJSON already exists at $NDJSON ($(du -h "$NDJSON" | cut -f1))"
    echo "    Delete it to re-export."
else
    echo ""
    echo ">>> Exporting CSLib to NDJSON (this takes ~5 minutes)..."
    mkdir -p "$PROJECT_DIR/test-data"

    # Build LEAN_PATH from all cslib packages
    LEAN_PATH=""
    for pkg in "$PARENT_DIR/cslib/.lake/packages/"*/; do
        p="${pkg}.lake/build/lib/lean"
        if [ -d "$p" ]; then
            LEAN_PATH="${LEAN_PATH:+$LEAN_PATH:}$p"
        fi
    done
    LEAN_PATH="$PARENT_DIR/cslib/.lake/build/lib/lean:$LEAN_PATH"
    export LEAN_PATH

    # Export the top-level Cslib module (includes all submodules)
    cd "$PARENT_DIR/cslib"
    "$PARENT_DIR/lean4export/.lake/build/bin/lean4export" Cslib > "$NDJSON"

    echo "    Exported: $(du -h "$NDJSON" | cut -f1) ($(wc -l < "$NDJSON") lines)"
fi

# ============================================================
# Step 5: Import into Ansatz store
# ============================================================

echo ""
echo ">>> Importing into Ansatz PSS filestore at $STORE_DIR..."
echo "    This takes ~2-5 minutes."

cd "$PROJECT_DIR"

# Compile Java kernel first
clj -T:build javac 2>/dev/null || true

clj -M -e "
(require '[ansatz.export.storage :as s])
(println \"Opening store at $STORE_DIR ...\")
(def store (s/open-store \"$STORE_DIR\"))
(println \"Starting import...\")
(time (s/import-ndjson-streaming! store \"$NDJSON\" \"cslib\" :verbose? true))
(println \"Done.\")
"

echo ""
echo "=== CSLib Setup Complete ==="
echo ""
echo "Store: $STORE_DIR ($(du -sh "$STORE_DIR" | cut -f1))"
echo ""
echo "To use in Clojure:"
echo "  (require '[ansatz.core :as a])"
echo "  (a/init! \"$STORE_DIR\" \"cslib\")"
echo ""
echo "Available verified algorithms:"
echo "  - MergeSort (correctness + O(n log n) complexity proof)"
echo "  - Automata (DFA, NFA, ε-NFA, Büchi, powerset construction)"
echo "  - Lambda Calculus (untyped, STLC, System F-sub, confluence proofs)"
echo "  - Combinatory Logic (SKI, bracket abstraction)"
echo "  - LTS (bisimulation, simulation, trace equivalence)"
echo "  - Turing Machines (single-tape, polynomial time)"
echo "  - Linear Logic (CLL, cut elimination)"
echo ""
echo "Example:"
echo "  (def ci (env/lookup (a/env) (name/from-string \"Cslib.Algorithms.Lean.TimeM.mergeSort_correct\")))"
echo "  ;; => theorem: mergeSort produces a sorted permutation of the input"
echo ""
