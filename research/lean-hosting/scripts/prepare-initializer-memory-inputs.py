"""Extract initializer-only benchmark inputs from the authenticated IR index.
Run from research/lean-hosting. No declarations, guest state or stores are created.
The suffix extraction relies on this exact pinned canonical index, not arbitrary JSON.
"""
import argparse
import hashlib
import json
import mmap
from pathlib import Path

INDEX = "74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e"
OVERLAYS = ["target/runtime-compile-shim-source.jsonl", "target/kernel-bridge-shim-source.jsonl",
            "target/kernel-bridge-shim-declarations-source.jsonl", "target/kernel-control-shim-source.jsonl",
            "target/runtime-compile-shim-files-source.jsonl", "target/module-data-transport-header-source.jsonl",
            "fixtures/kernel-encoding.jsonl", "target/lean-export-aliases.jsonl"]

def sha(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()

def prepare(output):
    root = Path(".")
    captures = json.loads((root / "measurements/full-init-assembly.json").read_text(encoding="utf-8"))["preparation-inputs-after-run"]
    index = root / "target/parser-module-store/indexes" / (INDEX + ".json")
    assert sha(index) == INDEX, "Pinned index changed"
    with index.open("rb") as source, mmap.mmap(source.fileno(), 0, access=mmap.ACCESS_READ) as mapped:
        marker = b'],"manifests":['
        offset = mapped.find(marker)
        assert offset >= 0, "Pinned canonical index framing differs"
        suffix = json.loads(b'{"manifests":[' + mapped[offset + len(marker):])
    assert suffix["schema"] == "lean-ir-store/1"
    manifests = suffix["manifests"]
    hashes = {str(index): INDEX}
    for path in OVERLAYS:
        actual = sha(root / path)
        assert actual == captures[path]["sha256"], path
        hashes[path] = actual
        with (root / path).open(encoding="utf-8") as source:
            rows = [json.loads(line) for line in source]
        module_manifests = [row for row in rows if row.get("kind") == "manifest"]
        assert len(module_manifests) == 1 and rows[0] is module_manifests[0], path
        manifests.append(module_manifests[0])
    plans = {}
    for manifest in manifests:
        plan = manifest.get("initializationPlan")
        if plan is not None and plan is not False:
            key = json.dumps(plan["module"], ensure_ascii=False, separators=(",", ":"))
            plans[key] = plan
    value = {"schema": "initializer-memory-inputs/1", "index-sha256": INDEX,
             "input-sha256": hashes, "plans": list(plans.values()),
             "witness-sha256": captures["target/module-initializer-symbols.json"]["sha256"]}
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(value, separators=(",", ":"), ensure_ascii=False) + "\n")
    print(json.dumps({"plans": len(plans), "bytes": output.stat().st_size, "sha256": sha(output)}))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    prepare(parser.parse_args().output)
