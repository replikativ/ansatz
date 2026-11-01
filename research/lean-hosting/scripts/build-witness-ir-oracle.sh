#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
leanir_toolchain=leanprover/lean4:v4.33.1
leanir_sysroot="$(lean +"$leanir_toolchain" --print-prefix)"
[[ "$(lean +"$leanir_toolchain" --githash)" == 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 ]]
mkdir -p target/witness-ir-value
# Compile SourceModuleExport/SourceModuleImport into target first, as documented
# by the owned source-module oracle. No native Environment is transported.
LEAN_NUM_THREADS=1 lean +"$leanir_toolchain" --root=lean \
  -o target/witness-ir-value/RuntimeCompileShim.olean \
  -c target/witness-ir-value/RuntimeCompileShim.c lean/RuntimeCompileShim.lean
cc -O0 -shared -fPIC -I "$leanir_sysroot/include" \
  target/witness-ir-value/RuntimeCompileShim.c -L "$leanir_sysroot/lib/lean" \
  -lleanshared -Wl,-rpath,"$leanir_sysroot/lib/lean" \
  -o target/witness-ir-value/libRuntimeCompileShim.so
c++ -std=c++17 -O1 -shared -fPIC -I "$leanir_sysroot/include" \
  native/IRValueTransport.cpp -L "$leanir_sysroot/lib/lean" \
  -lleanshared -Wl,-rpath,"$leanir_sysroot/lib/lean" \
  -o target/witness-ir-value/libIRValueTransport.so
# The relative path determines the private boxed extern name in the C++ oracle.
LEAN_PATH=target/witness-ir-value:target LEAN_NUM_THREADS=1 \
  lean +"$leanir_toolchain" \
  --load-dynlib=target/witness-ir-value/libRuntimeCompileShim.so \
  --load-dynlib=target/witness-ir-value/libIRValueTransport.so \
  lean/IRValueWitnessOracle.lean
# Never overwrite a previously adopted producer artifact during a rebuild.
LEAN_SYSROOT="$leanir_sysroot" LEAN_NUM_THREADS=1 target/lean-ir-export \
  --source lean/RuntimeCompileShim.lean --local RuntimeCompileShim \
  > target/witness-ir-value/RuntimeCompileShim.source.jsonl.partial
mv target/witness-ir-value/RuntimeCompileShim.source.jsonl.partial \
  target/witness-ir-value/RuntimeCompileShim.source.jsonl
