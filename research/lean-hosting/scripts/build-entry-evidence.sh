#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Explicit research build only. Never replace the accepted lean-ir-export binary.
# The caller supplies an already installed pinned toolchain; no elan download.
: "${LEAN_SYSROOT:?Set LEAN_SYSROOT to the installed official Lean 4.33.1 toolchain}"
if [[ -r /proc/meminfo ]]; then
  awk '/MemAvailable:/ { if ($2 < 2097152) exit 1 }' /proc/meminfo || {
    echo 'Refusing native helper build below the 2 GiB available-memory floor' >&2
    exit 1
  }
fi
expected=819816b2e0a3bf405af45ae5c7af2491d8f5bee6
actual="$("$LEAN_SYSROOT/bin/lean" --githash)"
[[ "$actual" == "$expected" ]] || { echo 'Installed compiler pin differs' >&2; exit 1; }
mkdir -p target/native-entry-evidence
"$LEAN_SYSROOT/bin/lean" --root=lean \
  -o target/native-entry-evidence/NativeEntryEvidence.olean \
  -c target/native-entry-evidence/NativeEntryEvidence.c lean/NativeEntryEvidence.lean
"$LEAN_SYSROOT/bin/leanc" -O2 -rdynamic \
  -o target/native-entry-evidence/lean-native-entry-evidence \
  target/native-entry-evidence/NativeEntryEvidence.c
