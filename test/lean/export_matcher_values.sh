#!/usr/bin/env bash
# String's decidable equality and the Prod matchers are absent from the medium
# Init tier. Export their closures for value cases and matcher conformance.
set -euo pipefail
cd "$(dirname "$0")/../.."
matcher_toolchain_bin=${LEAN_TOOLCHAIN_BIN:-"$HOME/.elan/toolchains/leanprover--lean4---v4.33.1/bin"}
matcher_exporter=${LEAN4EXPORT:-"$HOME/Development/lean4export/.lake/build/bin/lean4export"}
matcher_tmp=$(mktemp -d /tmp/ansatz-matcher-values.XXXXXX)
trap 'rm -rf "$matcher_tmp"' EXIT
PATH="$matcher_toolchain_bin:$PATH" \
  "$matcher_exporter" Init -- String.decEq instDecidableEqString True \
    Prod.Lex.instDecidableRelOfDecidableEq.match_1 \
    Prod.Lex.instDecidableRelOfDecidableEq.match_3 \
    Prod.Lex.instDecidableRelOfDecidableEq.match_5 Prod.lex.match_1 \
  | gzip -n > "$matcher_tmp/matcher-values.ndjson.gz"
mv "$matcher_tmp/matcher-values.ndjson.gz" test-data/kernel-reference/matcher-values.ndjson.gz
