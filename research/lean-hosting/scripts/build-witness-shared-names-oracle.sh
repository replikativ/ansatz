#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
leanir_toolchain=leanprover/lean4:v4.33.1
leanir_sysroot="$(lean +"$leanir_toolchain" --print-prefix)"
[[ "$(lean +"$leanir_toolchain" --githash)" == 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 ]]
mkdir -p target/witness-ir-shared-names
LEAN_NUM_THREADS=1 lean +"$leanir_toolchain" --root=lean \
  -o target/witness-ir-shared-names/RuntimeCompileShim.olean \
  -c target/witness-ir-shared-names/RuntimeCompileShim.c lean/RuntimeCompileShim.lean
cc -O0 -shared -fPIC -I "$leanir_sysroot/include" \
  target/witness-ir-shared-names/RuntimeCompileShim.c -L "$leanir_sysroot/lib/lean" \
  -lleanshared -Wl,-rpath,"$leanir_sysroot/lib/lean" \
  -o target/witness-ir-shared-names/libRuntimeCompileShim.so
LEAN_PATH=target/witness-ir-shared-names:target LEAN_NUM_THREADS=1 \
  lean +"$leanir_toolchain" \
  --load-dynlib=target/witness-ir-shared-names/libRuntimeCompileShim.so \
  lean/IRSharedNamesWitnessOracle.lean
# Rebuild into a separate candidate path, preserving adopted linear bytes.
LEAN_SYSROOT="$leanir_sysroot" LEAN_NUM_THREADS=1 target/lean-ir-export \
  --source lean/RuntimeCompileShim.lean --local RuntimeCompileShim \
  > target/witness-ir-shared-names/RuntimeCompileShim.source.jsonl.partial
mv target/witness-ir-shared-names/RuntimeCompileShim.source.jsonl.partial \
  target/witness-ir-shared-names/RuntimeCompileShim.source.jsonl
