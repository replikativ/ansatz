#!/usr/bin/env python3
"""Byte inventory and portable provenance only; no compiler, VM or guest call."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = json.loads((root / "manifest.json").read_text())
expected = {item["file"]: item["sha256"] for item in manifest["sources"]}
actual = {p.relative_to(root).as_posix() for p in root.rglob("*")
          if p.is_file() and p != root / "manifest.json"}
assert actual == set(expected), (actual, set(expected))
for name, digest in expected.items():
    raw = (root / name).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == digest, name
    assert (b"/" + b"home/") not in raw and (b"/" + b"Users/") not in raw, name
assert expected["runner.clj"] == manifest["tested-runner-sha256"]
assert manifest["acceptance"]["hostedFrontend"] is False
assert manifest["acceptance"]["javaKernelChecked"] is False
for item in (manifest.get("entry-evidence-source", {}).get("files", []) +
             manifest.get("generic-local-project", {}).get("external-sources", [])):
    assert hashlib.sha256((root.parents[4] / item["file"]).read_bytes()).hexdigest() == item["sha256"], item["file"]
print(json.dumps({"source-files": len(expected), "byte-inventory": "PASS",
                  "native-or-JVM-executed": False,
                  "acceptance-origin": manifest["acceptance"]["origin"]}))
