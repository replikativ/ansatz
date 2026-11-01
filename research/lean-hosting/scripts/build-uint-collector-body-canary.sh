#!/usr/bin/env bash
# Explicit invocation only. Run under a separate memory/deadline process guard.
# Relative input and output paths resolve from research/lean-hosting.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
canary_output="${ANSATZ_UINT_CANARY_OUTPUT:-target/actual-uint-body-canary}"
canary_runtime=target/witness-ir-shared-names-linear
canary_transport=target/witness-ir-value/libIRValueTransport.so
canary_toolchain=leanprover/lean4:v4.33.1
canary_sysroot="$(env -u LEAN_SYSROOT -u LEAN_PATH lean +"$canary_toolchain" --print-prefix)"
[[ "$(LEAN_SYSROOT="$canary_sysroot" LEAN_PATH=target lean +"$canary_toolchain" --githash)" == 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 ]]
[[ ! -e "$canary_output" ]]
[[ -f "$canary_runtime/RuntimeCompileShim.olean" && -f "$canary_runtime/libRuntimeCompileShim.so" ]]
[[ -f "$canary_transport" ]]
mkdir "$canary_output"
cp lean/UIntCollectorBodyCanary.lean "$canary_output/UIntCollectorBodyCanary.lean"
cp native/UIntCollectorBodyAdapter.cpp "$canary_output/UIntCollectorBodyAdapter.cpp"
# Record exact selected producer objects/source before compilation or export.
sha256sum "$canary_output/UIntCollectorBodyCanary.lean" \
  "$canary_output/UIntCollectorBodyAdapter.cpp" \
  "$canary_runtime/RuntimeCompileShim.olean" "$canary_runtime/libRuntimeCompileShim.so" \
  "$canary_transport" native/ModuleDataTransport.cpp native/GuestJsonTransport.cpp native/IRValueTransport.cpp \
  > "$canary_output/producer-inputs.sha256"
# No copy of old ModuleDataTransport main/object and no native Environment data
# transport. The new library is just a tiny #eval boxed forwarding adapter.
c++ -std=c++17 -O1 -shared -fPIC -I "$canary_sysroot/include" \
  "$canary_output/UIntCollectorBodyAdapter.cpp" \
  -L "$PWD/target/witness-ir-value" -lIRValueTransport \
  -L "$canary_sysroot/lib/lean" -lleanshared \
  -Wl,-rpath,"$PWD/target/witness-ir-value" -Wl,-rpath,"$canary_sysroot/lib/lean" \
  -o "$canary_output/libUIntCollectorBodyAdapter.so"
sha256sum "$canary_output/libUIntCollectorBodyAdapter.so" >> "$canary_output/producer-inputs.sha256"
# A 64 MiB native stack is explicit and bounded, matching the actual deep-IR
# oracle requirement. LEAN_NUM_THREADS=1; RSS/deadline belong to the outer guard.
(ulimit -s 65536
 ANSATZ_UINT_CANARY_OUTPUT="$canary_output" LEAN_SYSROOT="$canary_sysroot" LEAN_PATH="$canary_runtime:target" LEAN_NUM_THREADS=1 \
  lean +"$canary_toolchain" \
  --load-dynlib="$canary_runtime/libRuntimeCompileShim.so" \
  --load-dynlib="$canary_transport" \
  --load-dynlib="$canary_output/libUIntCollectorBodyAdapter.so" \
  "$canary_output/UIntCollectorBodyCanary.lean") \
  > "$canary_output/build.log" 2>&1
# The existing independent checker accepts canary modules=[] and preserves the
# extra explicit FnBody/selection provenance. It never treats them as ModuleData.
for canary_part in body decl expected; do
  python3 native/check_module_data_transport.py \
    "$canary_output/uint-macro.$canary_part.jsonl" \
    --publish "$canary_output/uint-macro.$canary_part.verified.json" \
    > "$canary_output/$canary_part.check.json"
done
sha256sum "$canary_output/"*.jsonl "$canary_output/"*.verified.json \
  "$canary_output/"*.verified.json.index > "$canary_output/outputs.sha256"
