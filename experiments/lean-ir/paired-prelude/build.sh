#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
export LEAN_NUM_THREADS=1
: "${LEAN4EXPORT_SOURCE:?set LEAN4EXPORT_SOURCE to read-only lean4export checkout}"
pin=819816b2e0a3bf405af45ae5c7af2491d8f5bee6
toolchain=leanprover/lean4:v4.33.1
[[ $(lean +"$toolchain" --githash) == "$pin" ]]
sysroot=$(lean +"$toolchain" --print-prefix)
build=target/matched-prelude-producer
mkdir -p "$build"
# Recompile upstream exporter into this worktree; never alter its checkout.
lean +"$toolchain" --root="$LEAN4EXPORT_SOURCE" -o "$build/Export.olean" -c "$build/Export.c" "$LEAN4EXPORT_SOURCE/Export.lean"
export LEAN_PATH="$PWD/$build${LEAN_PATH:+:$LEAN_PATH}"
lean +"$toolchain" --root=paired-prelude -o "$build/Projection.olean" -c "$build/Projection.c" paired-prelude/Projection.lean
lean +"$toolchain" --root=paired-prelude -o "$build/ScalarCensus.olean" -c "$build/ScalarCensus.c" paired-prelude/ScalarCensus.lean
lean +"$toolchain" --root=paired-prelude -o "$build/MatchedPreludeProducer.olean" -c "$build/MatchedPreludeProducer.c" paired-prelude/MatchedPreludeProducer.lean
for unit in Export Projection ScalarCensus MatchedPreludeProducer; do
  cc -fPIC -O0 -I "$sysroot/include" -c "$build/$unit.c" -o "$build/$unit.o"
done
c++ -std=c++17 -fPIC -O1 -I "$sysroot/include" paired-prelude/Native.cpp \
  "$build/Export.o" "$build/Projection.o" "$build/ScalarCensus.o" "$build/MatchedPreludeProducer.o" \
  -L "$sysroot/lib/lean" -Wl,-rpath,"$sysroot/lib/lean" -rdynamic \
  -Wl,--no-as-needed -lgcc_s -Wl,--as-needed -lleanshared -o "$build/produce"
python3 paired-prelude/provenance.py "$LEAN4EXPORT_SOURCE" "$build/build-cohort.json"
