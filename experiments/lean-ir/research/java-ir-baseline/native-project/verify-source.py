#!/usr/bin/env python3
"""Byte inventory and portable provenance only; no compiler, VM or guest call."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / "manifest.json").read_text())
expected = {item["file"]: item["sha256"] for item in manifest["sources"]}
actual = {p.name for p in root.iterdir() if p.is_file() and p.name != "manifest.json"}
assert actual == set(expected), (actual, set(expected))
for name, digest in expected.items():
    raw = (root / name).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == digest, name
    assert (b"/" + b"home/") not in raw and (b"/" + b"Users/") not in raw, name
assert expected["runner.clj"] == manifest["tested-runner-sha256"]
assert manifest["acceptance"]["hostedFrontend"] is False
assert manifest["acceptance"]["javaKernelChecked"] is False
print(json.dumps({"source-files": len(expected), "byte-inventory": "PASS",
                  "native-or-JVM-executed": False,
                  "acceptance-origin": manifest["acceptance"]["origin"]}))
