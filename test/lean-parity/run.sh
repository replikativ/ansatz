#!/usr/bin/env bash
# Run the Lean parity corpus (test/lean-parity/{simp,kernel,dsl}/*.lean) with the Lean v4.36.0 toolchain.
# Each file asserts the outcome Lean produces (an `example` that only elaborates when simp
# produces the expected form, or `#guard_msgs` for an expected error/warning); any error fails.
# Usage: test/lean-parity/run.sh   (LEAN=/path/to/lean overrides the toolchain)
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
LEAN=${LEAN:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean}
"$LEAN" --version | grep -q "version 4.36.0" || { echo "need Lean v4.36.0 at $LEAN" >&2; exit 2; }
lib=$(cd "$(dirname "$LEAN")/../lib/lean" && pwd)
build=$(mktemp -d); trap 'rm -rf "$build"' EXIT
# register_simp_attr needs its own module
"$LEAN" -o "$build/ParitySimpSets.olean" "$here/simp/ParitySimpSets.lean" || { echo "FAIL ParitySimpSets.lean"; exit 1; }
fail=0; n=0
for f in "$here"/simp/*.lean "$here"/kernel/*.lean "$here"/dsl/*.lean; do
  [ -e "$f" ] || continue
  case "$(basename "$f")" in ParitySimpSets.lean) continue;; esac
  n=$((n+1))
  name="$(basename "$(dirname "$f")")/$(basename "$f")"
  if out=$(LEAN_PATH="$build:$lib" "$LEAN" "$f" 2>&1) && ! grep -q "error" <<<"$out"; then
    echo "ok   $name"
  else
    echo "FAIL $name"; echo "$out" | sed 's/^/     /'; fail=$((fail+1))
  fi
done
echo "$((n-fail))/$n passed"
[ "$fail" -eq 0 ]
