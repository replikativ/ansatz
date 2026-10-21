#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
mkdir -p target
lean +leanprover/lean4:v4.33.1 --root=lean \
  -o target/Export.olean -c target/Export.c lean/Export.lean
# Imported native frontend code resolves interpreter symbols from the executable.
# Without -rdynamic those symbols are unavailable even though compilation passes.
leanc +leanprover/lean4:v4.33.1 -O2 -rdynamic \
  -o target/lean-ir-export target/Export.c
