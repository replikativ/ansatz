#!/usr/bin/env bash
set -euo pipefail
# Usage: ./reproduce.sh /absolute/path/to/official/lean-sdk [n]
root=$(cd "$1" && pwd)
n=${2:-24}
source_dir=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d /tmp/lean-projection-regression.XXXXXX)
trap 'rm -rf "$work"' EXIT
unset LEAN_PATH LEAN_SYSROOT LD_LIBRARY_PATH LEAN_KERNEL_TRACE LEAN_KERNEL_TRACE_DECL || true
export LEAN_NUM_THREADS=1 LEAN_STACK_SIZE_KB=16384
"$root/bin/lean" --version
"$root/bin/lean" --githash
if "$root/bin/lean" --version | grep -q 'version 4.32.1,'; then
  # 4.33 added the maxRecDepth parameter; no other source difference.
  sed -e 's/addDeclCore 0 0 iterator/addDeclCore 0 iterator/' \
      -e 's/addDeclCore 100000 0 thm/addDeclCore 100000 thm/' \
      "$source_dir/Regression.lean" > "$work/Regression.lean"
else
  cp "$source_dir/Regression.lean" "$work/Regression.lean"
fi
cd "$work"
"$root/bin/lean" -c Regression.c Regression.lean
"$root/bin/leanc" -O2 -o regression Regression.c
# A fresh native process gives a fresh kernel heartbeat counter.
# Exit: 0 checked; 2 deterministic timeout; 1 other kernel error.
LEAN_SYSROOT="$root" ./regression "$n"
