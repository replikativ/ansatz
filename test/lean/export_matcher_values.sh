#!/usr/bin/env bash
# String's decidable equality is absent from the medium Init tier. Export its
# dependency closure for the generic matcher value-case regression.
set -euo pipefail
cd "$(dirname "$0")/../.."
matcher_toolchain_bin=${LEAN_TOOLCHAIN_BIN:-"$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin"}
matcher_exporter=${LEAN4EXPORT:-"$HOME/Development/lean4export/.lake/build/bin/lean4export"}
matcher_tmp=$(mktemp -d /tmp/ansatz-matcher-values.XXXXXX)
trap 'rm -rf "$matcher_tmp"' EXIT
"$matcher_toolchain_bin/lean" -R test/lean -o "$matcher_tmp/matcher_declarations.olean" test/lean/matcher_declarations.lean
LEAN_PATH="$matcher_tmp" PATH="$matcher_toolchain_bin:$PATH" \
  "$matcher_exporter" matcher_declarations -- String.decEq instDecidableEqString \
  | gzip -n > "$matcher_tmp/matcher-values.ndjson.gz"
mv "$matcher_tmp/matcher-values.ndjson.gz" test-data/kernel-reference/matcher-values.ndjson.gz
