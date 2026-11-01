#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
leanir_toolchain=leanprover/lean4:v4.33.1
leanir_sysroot="$(env -u LEAN_SYSROOT -u LEAN_PATH lean +"$leanir_toolchain" --print-prefix)"
export LEAN_SYSROOT="$leanir_sysroot"
export LEAN_PATH=target
[[ "$(lean +"$leanir_toolchain" --githash)" == 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 ]]
# Fresh producer output only; do not overwrite any adopted candidate.
[[ ! -e target/witness-ir-shared-names-linear ]]
mkdir -p target/witness-ir-shared-names-linear
LEAN_NUM_THREADS=1 lean +"$leanir_toolchain" --root=lean \
  -o target/witness-ir-shared-names-linear/RuntimeCompileShim.olean \
  -c target/witness-ir-shared-names-linear/RuntimeCompileShim.c lean/RuntimeCompileShim.lean
cc -O0 -shared -fPIC -I "$leanir_sysroot/include" \
  target/witness-ir-shared-names-linear/RuntimeCompileShim.c -L "$leanir_sysroot/lib/lean" \
  -lleanshared -Wl,-rpath,"$leanir_sysroot/lib/lean" \
  -o target/witness-ir-shared-names-linear/libRuntimeCompileShim.so
LEAN_PATH=target/witness-ir-shared-names-linear:target LEAN_NUM_THREADS=1 \
  lean +"$leanir_toolchain" \
  --load-dynlib=target/witness-ir-shared-names-linear/libRuntimeCompileShim.so \
  lean/IRSharedNamesLinearWitnessOracle.lean | tee target/witness-ir-shared-names-linear/oracle.log
# Real culprit coverage is separate from toy native parity. Deep actual IR may
# need a larger native stack, bounded here independently from the RSS guard.
(ulimit -s 65536
 LEAN_PATH=target/witness-ir-shared-names-linear:target LEAN_NUM_THREADS=1 \
  lean +"$leanir_toolchain" \
  --load-dynlib=target/witness-ir-shared-names-linear/libRuntimeCompileShim.so \
  lean/IRSharedNamesLinearInitOracle.lean) \
  | tee target/witness-ir-shared-names-linear/init-oracle.log
sha256sum target/witness-ir-shared-names-linear/init-original.json \
  target/witness-ir-shared-names-linear/init-shared-linear.json \
  | tee target/witness-ir-shared-names-linear/init-witness-sha256.txt
# Rebuild into a fresh candidate path, preserving ALL adopted artifacts.
LEAN_SYSROOT="$leanir_sysroot" LEAN_NUM_THREADS=1 target/lean-ir-export \
  --source lean/RuntimeCompileShim.lean --local RuntimeCompileShim \
  > target/witness-ir-shared-names-linear/RuntimeCompileShim.source.jsonl.partial
mv target/witness-ir-shared-names-linear/RuntimeCompileShim.source.jsonl.partial \
  target/witness-ir-shared-names-linear/RuntimeCompileShim.source.jsonl
# Independently check every previously pinned declaration, including unadopted
# linear helpers. Compare parsed rows exactly; do not normalize IR or metadata.
python3 - <<'PYCODE'
import hashlib, json
from pathlib import Path
old = Path("target/runtime-compile-shim-ir-shared-names-source.jsonl")
assert hashlib.sha256(old.read_bytes()).hexdigest() == "9864fa3afbf521fa541ef0a00931c34e237ea6538582ddad0746acf5e8e5bed8"
new = Path("target/witness-ir-shared-names-linear/RuntimeCompileShim.source.jsonl")
def rows(path):
    items = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    result = {}
    for row in items[1:]:
        key = json.dumps(row["name"], ensure_ascii=False, separators=(",", ":"))
        assert key not in result, "duplicate declaration"
        result[key] = row
    return items[0], result
a, aa = rows(old); b, bb = rows(new)
assert a == b, "producer manifest changed"
for name, row in aa.items(): assert bb.get(name) == row, "old declaration changed: " + name
assert len(bb) > len(aa), "missing additive declarations"
print(json.dumps({"oldRows": len(aa), "newRows": len(bb), "oldRowsUnchanged": True,
                  "sha256": hashlib.sha256(new.read_bytes()).hexdigest()}))
PYCODE
LEAN_PATH=target/witness-ir-shared-names-linear:target LEAN_SYSROOT="$leanir_sysroot" LEAN_NUM_THREADS=1 target/lean-ir-export \
  --source lean/IRSharedNamesLinearGuestProbe.lean --local IRSharedNamesLinearGuestProbe \
  > target/witness-ir-shared-names-linear/GuestProbe.source.jsonl.partial
mv target/witness-ir-shared-names-linear/GuestProbe.source.jsonl.partial \
  target/witness-ir-shared-names-linear/GuestProbe.source.jsonl
