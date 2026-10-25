#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
leanir_toolchain=leanprover/lean4:v4.33.1
leanir_sysroot="$(lean +"$leanir_toolchain" --print-prefix)"
leanir_commit="$(lean +"$leanir_toolchain" --githash)"
[[ "$leanir_commit" == 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 ]]
mkdir -p target
lean +"$leanir_toolchain" --root=lean -o target/ModuleDataTransport.olean \
  -c target/ModuleDataTransport.c lean/ModuleDataTransport.lean
# PIC is essential: executable COPY relocations otherwise hide shared-library
# initialized globals behind null executable-local copies (e.g. Lean.githash).
cc -fPIC -O0 -I "$leanir_sysroot/include" -c target/ModuleDataTransport.c -o target/ModuleDataTransport-lean.o
# libleanshared exports its bundled unwinder. Load the matching system GCC
# unwinder first for this GCC-built helper, or C++ rejection exceptions terminate
# instead of reaching the local handler.
c++ -std=c++17 -fPIC -O1 -I "$leanir_sysroot/include" native/ModuleDataTransport.cpp \
  target/ModuleDataTransport-lean.o -L "$leanir_sysroot/lib/lean" \
  -Wl,-rpath,"$leanir_sysroot/lib/lean" -rdynamic -Wl,--no-as-needed -lgcc_s -Wl,--as-needed -lleanshared -o target/ModuleDataTransport
printf 'Built target/ModuleDataTransport against %s\n' "$leanir_commit"
