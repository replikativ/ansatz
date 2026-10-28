#!/usr/bin/env bash
# Additional native oracle closures for String value cases and Prod matcher conformance.
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
# The coordinated Init companion only covers its selected kernel declarations.
# Keep the extra oracle's native MatcherInfo beside its checked kernel closure.
LEAN_SYSROOT="${matcher_toolchain_bin%/bin}" "$matcher_toolchain_bin/lean" \
  --run scripts/dump_matchers.lean Init > "$matcher_tmp/matchers.ndjson"
python3 - "$matcher_tmp/matchers.ndjson" "$matcher_tmp/oracle-matchers.ndjson" <<'PYTHON'
import json
import sys

wanted = {"Prod.Lex.instDecidableRelOfDecidableEq.match_1",
          "Prod.Lex.instDecidableRelOfDecidableEq.match_3",
          "Prod.Lex.instDecidableRelOfDecidableEq.match_5", "Prod.lex.match_1"}
rows = {}
with open(sys.argv[1]) as source:
    for line in source:
        row = json.loads(line)
        if row["name"] in wanted:
            if row["name"] in rows:
                raise SystemExit("Duplicate oracle matcher metadata")
            rows[row["name"]] = line.strip()
if set(rows) != wanted:
    raise SystemExit("Missing oracle matcher metadata")
with open(sys.argv[2], "w") as destination:
    for name in sorted(rows):
        destination.write(rows[name] + "\n")
PYTHON
mv "$matcher_tmp/matcher-values.ndjson.gz" test-data/kernel-reference/matcher-values.ndjson.gz
mv "$matcher_tmp/oracle-matchers.ndjson" test-data/kernel-reference/matcher-values-matchers.ndjson
