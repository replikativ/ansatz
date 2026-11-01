#!/usr/bin/env python3
"""Source inventory/equivalence only. Does not run Lean, a JVM or guest code."""
import hashlib
import json
from pathlib import Path

directory = Path(__file__).resolve().parent
repo = Path(__file__).resolve().parents[6]
manifest = json.loads((directory / "manifest.json").read_bytes())
for item in manifest["files"]:
    path = repo / item["file"]
    assert path.is_file() and not path.is_symlink(), item["file"]
    raw = path.read_bytes()
    assert len(raw) == item["bytes"], item["file"]
    assert hashlib.sha256(raw).hexdigest() == item["sha256"], item["file"]
    assert (b"/" + b"home/") not in raw and (b"/" + b"Users/") not in raw, item["file"]

entry = (repo / "experiments/lean-ir/lean/NativeEntryEvidence.lean").read_text()
source = (repo / "experiments/lean-ir/lean/NativeStartupEvidence.lean").read_text()
segments = {
    "entry-core": entry[entry.index("private def nameJson"):entry.index("private def expectedType")],
    "entry-ir": entry[entry.index("-- Actual pinned original interpreter lookup"):entry.index("private def entry (env")],
    "entry-rows": entry[entry.index("private def rows (env"):entry.index("private def initializerInventory")],
}
for label, expected in segments.items():
    actual = source.split(f"-- BEGIN copied {label}\n", 1)[1].split(f"-- END copied {label}", 1)[0]
    assert actual == expected, label
for item in manifest["unchangedAcceptedSources"]:
    assert hashlib.sha256((repo / item["file"]).read_bytes()).hexdigest() == item["sha256"], item["file"]

fixtures = repo / "experiments/lean-ir/test/fixtures/native-startup-evidence"
for path in fixtures.glob("*-request.json"):
    raw = path.read_bytes()
    assert len(raw) <= 65536
    document = json.loads(raw)
    assert document["schema"] == "lean-native-startup-requests/1"
    assert 1 <= len(document["requestedImports"]) <= 128
crlf = (fixtures / "header-crlf-unicode.lean").read_bytes()
assert b"\r\n" in crlf and "🦉" in crlf.decode("utf-8")
assert b"\r\n" == crlf[crlf.index(b"\r\n"):crlf.index(b"\r\n") + 2]
checks = (fixtures / "SelectionChecks.lean").read_text()
assert checks.count("#guard ") == 9
assert isinstance(manifest["acceptance"]["nativeCompiled"], bool)
assert isinstance(manifest["acceptance"]["JVMExecuted"], bool)
print(json.dumps({"sourceFiles": len(manifest["files"]), "copiedRegions": len(segments),
                  "unchangedAcceptedSources": len(manifest["unchangedAcceptedSources"]),
                  "sourceInventory": "PASS", "nativeOrJVMExecuted": False,
                  "runtimeAcceptance": "not established by this source verifier"}))
