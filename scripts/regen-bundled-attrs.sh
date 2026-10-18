#!/usr/bin/env bash
# Historical entry point: individual writes break the six-artifact bundle contract.
set -euo pipefail
cat >&2 <<'MESSAGE'
Direct bundled-resource regeneration has been retired. Generate a coordinated
candidate in a new staging directory instead:

  python3 scripts/generate-bundle.py --exporter-source /path/to/lean4export \
    --lean-root /path/to/pinned/lean/toolchain --output target/bundle-candidate

The generator records all six artifacts and their checker/producer inputs.
Review validation.edn and complete activation/WF acceptance before promotion.
It does not replace shipped resources or development fixtures.
MESSAGE
exit 2
