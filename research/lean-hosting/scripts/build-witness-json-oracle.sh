#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
leanir_toolchain=leanprover/lean4:v4.33.1
leanir_sysroot="$(lean +"$leanir_toolchain" --print-prefix)"
[[ "$(lean +"$leanir_toolchain" --githash)" == 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 ]]
mkdir -p target/witness-json-value
for leanir_module in SourceModuleExport SourceModuleImport; do
  if [[ ! -f "target/$leanir_module.olean" ]]; then
    LEAN_PATH=target LEAN_NUM_THREADS=1 lean +"$leanir_toolchain" --root=lean \
      -o "target/$leanir_module.olean" "lean/$leanir_module.lean"
  fi
done
LEAN_NUM_THREADS=1 lean +"$leanir_toolchain" --root=lean \
  -o target/witness-json-value/RuntimeCompileShim.olean \
  -c target/witness-json-value/RuntimeCompileShim.c lean/RuntimeCompileShim.lean
cc -O0 -shared -fPIC -I "$leanir_sysroot/include" \
  target/witness-json-value/RuntimeCompileShim.c -L "$leanir_sysroot/lib/lean" \
  -lleanshared -Wl,-rpath,"$leanir_sysroot/lib/lean" \
  -o target/witness-json-value/libRuntimeCompileShim.so
c++ -std=c++17 -O1 -shared -fPIC -I "$leanir_sysroot/include" \
  native/GuestJsonTransport.cpp -L "$leanir_sysroot/lib/lean" \
  -lleanshared -Wl,-rpath,"$leanir_sysroot/lib/lean" \
  -o target/witness-json-value/libGuestJsonTransport.so
# This relative oracle path deliberately determines its private extern's boxed
# symbol, supplied by GuestJsonTransport.cpp. Do not add --root=lean here.
LEAN_PATH=target/witness-json-value:target LEAN_NUM_THREADS=1 \
  lean +"$leanir_toolchain" \
  --load-dynlib=target/witness-json-value/libRuntimeCompileShim.so \
  --load-dynlib=target/witness-json-value/libGuestJsonTransport.so \
  lean/GuestJsonWitnessOracle.lean
# The existing pinned exporter must already be built via build-exporter.sh.
LEAN_SYSROOT="$leanir_sysroot" LEAN_NUM_THREADS=1 target/lean-ir-export \
  --source lean/RuntimeCompileShim.lean --local RuntimeCompileShim \
  > target/runtime-compile-shim-json-value-source.jsonl
