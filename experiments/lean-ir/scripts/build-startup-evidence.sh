#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Explicit research build. Root resource admission/supervision is required.
# Never overwrite accepted Export or NativeEntryEvidence products.
: "${LEAN_SYSROOT:?Set LEAN_SYSROOT to the installed official Lean 4.33.1 toolchain}"
stage="${1:?Choose emit, selection-checks or link; each needs root resource supervision}"
[[ $# == 1 ]] || { echo 'Exactly one build stage required' >&2; exit 1; }
if [[ -r /proc/meminfo ]]; then
  awk '/MemAvailable:/ { if ($2 < 2097152) exit 1 }' /proc/meminfo || {
    echo 'Refusing native helper build below the 2 GiB available-memory floor' >&2
    exit 1
  }
fi
export LEAN_NUM_THREADS=1
export MALLOC_ARENA_MAX=1
expected=819816b2e0a3bf405af45ae5c7af2491d8f5bee6
actual="$("$LEAN_SYSROOT/bin/lean" --githash)"
[[ "$actual" == "$expected" ]] || { echo 'Installed compiler pin differs' >&2; exit 1; }
mkdir -p target/native-startup-evidence
case "$stage" in
  emit)
    "$LEAN_SYSROOT/bin/lean" --root=lean \
      -o target/native-startup-evidence/NativeStartupEvidence.olean \
      -c target/native-startup-evidence/NativeStartupEvidence.c lean/NativeStartupEvidence.lean
    ;;
  selection-checks)
    LEAN_PATH="$PWD/target/native-startup-evidence:$LEAN_SYSROOT/lib/lean" \
      "$LEAN_SYSROOT/bin/lean" --root=test/fixtures/native-startup-evidence \
      test/fixtures/native-startup-evidence/SelectionChecks.lean
    ;;
  link)
    "$LEAN_SYSROOT/bin/leanc" -O2 -rdynamic \
      -o target/native-startup-evidence/lean-native-startup-evidence \
      target/native-startup-evidence/NativeStartupEvidence.c
    ;;
  *) echo 'Unknown build stage; choose emit, selection-checks or link' >&2; exit 1 ;;
esac
