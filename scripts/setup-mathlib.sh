#!/usr/bin/env bash
# Setup Ansatz Mathlib store from scratch.
#
# Prerequisites:
#   - Lean 4 (elan): https://github.com/leanprover/elan
#   - Java 21+
#   - Clojure CLI 1.12+
#
# This script:
#   1. Clones lean4export and mathlib4 (if not present) and checks out the PINNED release
#   2. Builds lean4export on Mathlib's toolchain
#   3. Exports Mathlib to NDJSON
#   4. Dumps the @[instance] registry (scripts/dump_instances.lean)
#   5. Dumps the @[simp]/@[csimp]/@[extern] attributes (scripts/dump_attrs.lean)
#   6. Dumps modules + docstrings for the catalogue (scripts/dump_modules.lean)
#   7. Imports into an Ansatz store — one command, complete store
#
# Usage:
#   ./scripts/setup-mathlib.sh [STORE_DIR]
#   MATHLIB_TAG=v4.34.0 ./scripts/setup-mathlib.sh      # build a different release
#   IMPORT_HEAP=6g ./scripts/setup-mathlib.sh           # importer heap (default 8g)
#
# Default STORE_DIR: the durable ansatz.store data-root (XDG); /var/tmp erodes (systemd-tmpfiles)
#
# PINNING. A store is a build of ONE Mathlib release on ONE Lean toolchain, and every
# artifact below (export, registry, attributes, modules) must come from that same pair —
# the manifest records them as provenance. Mathlib tags releases by Lean version;
# lean4export tags by Lean MINOR version and is built here on Mathlib's exact toolchain.
# An unpinned `master` clone made "latest" mean "whenever this machine cloned it".

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
DEFAULT_ROOT="${ANSATZ_STORE_DIR:-${XDG_DATA_HOME:-$HOME/.local/share}/ansatz/stores}"
STORE_DIR="${1:-$DEFAULT_ROOT/mathlib}"
PARENT_DIR="$(dirname "$PROJECT_DIR")"
LIB_DIR="$PARENT_DIR/mathlib4"
MATHLIB_TAG="${MATHLIB_TAG:-v4.33.1}"
LEAN4EXPORT_TAG="${LEAN4EXPORT_TAG:-v4.33.0}"

# Check out `ref` in a clone, refusing to discard someone's uncommitted work.
checkout_pinned() {
    local dir="$1" ref="$2"
    # (lean-toolchain is excluded: this script rewrites lean4export's to Mathlib's, see below)
    if [ -n "$(git -C "$dir" status --porcelain --untracked-files=no -- . ':!lean-toolchain')" ]; then
        echo "ERROR: $dir has uncommitted changes; commit or stash them before pinning to $ref" >&2
        exit 1
    fi
    if [ "$(git -C "$dir" describe --tags --exact-match 2>/dev/null || true)" != "$ref" ]; then
        echo ">>> Checking out $ref in $dir"
        git -C "$dir" fetch -q --tags origin
        git -C "$dir" checkout -q "$ref"
    else
        echo ">>> $dir is at $ref"
    fi
}

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

checkout_pinned "$LIB_DIR" "$MATHLIB_TAG"
checkout_pinned "$PARENT_DIR/lean4export" "$LEAN4EXPORT_TAG"
TOOLCHAIN="$(cat "$LIB_DIR/lean-toolchain")"
# lean4export must run on the toolchain that built Mathlib's oleans (a patch release apart from
# its own tag is fine — the export API does not move within a minor version).
if [ "$(cat "$PARENT_DIR/lean4export/lean-toolchain")" != "$TOOLCHAIN" ]; then
    echo ">>> Aligning lean4export to Mathlib's toolchain $TOOLCHAIN"
    echo "$TOOLCHAIN" > "$PARENT_DIR/lean4export/lean-toolchain"
fi
echo ">>> Fetching Mathlib's olean cache for $MATHLIB_TAG (idempotent; several GB the first time)"
(cd "$LIB_DIR" && lake exe cache get)

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

NDJSON="$PROJECT_DIR/test-data/mathlib-$MATHLIB_TAG.ndjson"
if [ -f "$NDJSON" ]; then
    echo ""
    echo ">>> NDJSON already exists at $NDJSON ($(du -h "$NDJSON" | cut -f1))"
    echo "    Delete it to re-export."
else
    echo ""
    echo ">>> Exporting Mathlib to NDJSON (this takes ~5 minutes)..."
    mkdir -p "$PROJECT_DIR/test-data"
    # Preserve mdata wrappers so imported declarations can match Lean's
    # kernel trace/reduction behavior more closely.
    cd "$PARENT_DIR/mathlib4"
    # tmp + mv: a killed export must not leave a truncated file the "already exists" check reuses
    lake env "$PARENT_DIR/lean4export/.lake/build/bin/lean4export" --export-mdata Mathlib > "$NDJSON.partial" \
        && mv "$NDJSON.partial" "$NDJSON"
    echo "    Exported: $(du -h "$NDJSON" | cut -f1)"
fi

# ============================================================
# Step 4: Dump Lean's @[instance] registry (co-generated with the export)
# ============================================================
# Instances are NOT in the kernel export either. scripts/dump_instances.lean walks Lean's instance
# extension in MODULE ORDER with the REAL priorities — both load-bearing: synthesis tries
# instances by priority, most recently declared first among equals (Lean's SynthInstance), and
# a registry without that order picks grind's internal `Semiring.ofNat` for `(1 : ℝ)` instead
# of `One.toOfNat1`. The importer folds it into the store's derived `:instances` blob; the raw
# file is kept under <store>/inputs/ for regeneration.

INSTANCES_TSV="$PROJECT_DIR/test-data/mathlib-$MATHLIB_TAG-instances.tsv"
if [ -f "$INSTANCES_TSV" ]; then
    echo ""
    echo ">>> instances already dumped at $INSTANCES_TSV ($(wc -l < "$INSTANCES_TSV") lines). Delete it to re-dump."
else
    echo ""
    echo ">>> Dumping Mathlib @[instance] registry into $INSTANCES_TSV ..."
    cd "$LIB_DIR"
    lake env lean --run "$PROJECT_DIR/scripts/dump_instances.lean" Mathlib > "$INSTANCES_TSV.partial" \
        && mv "$INSTANCES_TSV.partial" "$INSTANCES_TSV"
    echo "    Wrote $(wc -l < "$INSTANCES_TSV") instances"
fi

# ============================================================
# Step 5: Dump Lean attributes (co-generated with the export)
# ============================================================
# @[simp]/@[csimp]/@[extern] are NOT in the kernel export — dump them from the SAME library +
# toolchain that produced $NDJSON. The importer folds them into the store; the raw file is kept
# under <store>/inputs/ for regeneration. Co-generating here means the attrs can never drift
# from the store across a toolchain bump.

ATTRS_GZ="$PROJECT_DIR/test-data/mathlib-$MATHLIB_TAG-attrs.ndjson.gz"
if [ -f "$ATTRS_GZ" ]; then
    echo ""
    echo ">>> attrs already dumped at $ATTRS_GZ ($(zcat "$ATTRS_GZ" | wc -l) lines). Delete it to re-dump."
else
    echo ""
    echo ">>> Dumping Mathlib @[simp]/@[csimp]/@[extern] into $ATTRS_GZ ..."
    cd "$LIB_DIR"
    lake env lean --run "$PROJECT_DIR/scripts/dump_attrs.lean" Mathlib | gzip -c > "$ATTRS_GZ.partial" \
        && mv "$ATTRS_GZ.partial" "$ATTRS_GZ"
    echo "    Wrote $(zcat "$ATTRS_GZ" | wc -l) attribute lines"
fi

# ============================================================
# Step 6: Dump modules + docstrings (the catalogue's :decl/module and :decl/doc)
# ============================================================

MODULES_GZ="$PROJECT_DIR/test-data/mathlib-$MATHLIB_TAG-modules.ndjson.gz"
if [ -f "$MODULES_GZ" ]; then
    echo ""
    echo ">>> modules already dumped at $MODULES_GZ. Delete it to re-dump."
else
    echo ""
    echo ">>> Dumping Mathlib modules + docstrings into $MODULES_GZ ..."
    cd "$LIB_DIR"
    lake env lean --run "$PROJECT_DIR/scripts/dump_modules.lean" Mathlib | gzip -c > "$MODULES_GZ.partial" \
        && mv "$MODULES_GZ.partial" "$MODULES_GZ"
    echo "    Wrote $(zcat "$MODULES_GZ" | wc -l) declarations"
fi

# ============================================================
# Step 7: Import — ONE command produces the complete store
# ============================================================
# Blobs, attributes, instances, matchers, recall keys, @[simp] keys + trie, the catalogue
# (when datahike is on the classpath), the inputs, and the manifest LAST (ansatz.import).
# The keying passes run on every core; Mathlib takes on the order of an hour.

if [ -f "$STORE_DIR/manifest.edn" ]; then
    echo ""
    echo ">>> Store already complete at $STORE_DIR (manifest present). Delete it to re-import."
else
    echo ""
    echo ">>> Importing into $STORE_DIR ..."
    cd "$PROJECT_DIR"
    clj -T:build javac 2>/dev/null || true
    LIB_REV="$(git -C "$LIB_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
    EXPORT_REV="$(git -C "$PARENT_DIR/lean4export" rev-parse HEAD 2>/dev/null || echo unknown)"
    clj "-J-Xmx${IMPORT_HEAP:-8g}" -M:datahike -m ansatz.import "$STORE_DIR" "$NDJSON" "mathlib" "$ATTRS_GZ" "$INSTANCES_TSV" "$MODULES_GZ" \
        "lean/toolchain=$TOOLCHAIN" "library/tag=$MATHLIB_TAG" "library/rev=$LIB_REV" "lean4export/rev=$EXPORT_REV"
fi

echo ""
echo "=== Setup Complete ==="
echo ""
echo "Store: $STORE_DIR ($(du -sh "$STORE_DIR" | cut -f1))"
echo ""
echo "To use in Clojure:"
echo "  (require '[ansatz.core :as a])"
echo "  (a/init! \"mathlib\")"
echo ""
