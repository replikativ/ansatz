"""Read-only portable inventory and original-row audit; no runtime execution."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
inventory = json.loads((root / "inventory.json").read_text())
expected = {record["path"] for record in inventory["files"]} | {"inventory.json"}
actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
assert actual == expected, (actual - expected, expected - actual)
for record in inventory["files"]:
    path = root / record["path"]
    assert not path.is_symlink()
    raw = path.read_bytes()
    assert len(raw) == record["bytes"]
    assert hashlib.sha256(raw).hexdigest() == record["sha256"], record["path"]
capture = root / "captures/prior-cas"
manifest = json.loads((capture / "manifest.json").read_text())
stream = (capture / "declarations.jsonl").read_bytes()
assert hashlib.sha256(stream).hexdigest() == manifest["declarations"]["sha256"]
lines = stream.splitlines()
assert len(lines) == len(manifest["rows"]) == manifest["rowCount"] == 63
for raw, record in zip(lines, manifest["rows"]):
    assert hashlib.sha256(raw).hexdigest() == record["sha256"]
    assert len(raw) == record["bytes"]
    assert json.loads(raw)["name"] == record["name"]
print(json.dumps({"files": len(inventory["files"]), "originalRows": len(lines),
                  "runtimeExecuted": False}))
