#!/usr/bin/env python3
"""Strict current source layer plus historical Git identity; no runtime acceptance.

Old source/fixture/receipt manifests remain byte-exact. Their original verifier
implementations are recoverable at the recorded source commit. Current wrapper
commands verify this explicit relocation layer, never pretend renamed Java
classes or edited loaders were executed by the earlier accepted runtime.
"""
import hashlib
import json
from pathlib import Path
import subprocess

HOSTING = Path(__file__).resolve().parents[1]
REPO = HOSTING.parents[1]
HISTORY = HOSTING / "history"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def relative(path):
    assert isinstance(path, str) and not Path(path).is_absolute(), path
    assert ".." not in Path(path).parts and "\n" not in path, path
    return REPO / path


def historical_blobs(records, commit):
    process = subprocess.Popen(["git", "cat-file", "--batch"], cwd=REPO,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for record in records:
            process.stdin.write(f"{commit}:{record['original']}\n".encode())
            process.stdin.flush()
            header = process.stdout.readline().decode().strip().split()
            assert len(header) == 3 and header[1] == "blob", record["original"]
            size = int(header[2])
            assert 0 <= size <= 16 * 1048576, record["original"]
            data = bytearray()
            while len(data) < size:
                chunk = process.stdout.read(min(65536, size - len(data)))
                assert chunk, record["original"]
                data.extend(chunk)
            assert process.stdout.read(1) == b"\n"
            yield record, bytes(data)
    finally:
        process.stdin.close()
        process.stdout.close()
        assert process.wait() == 0


def main():
    moves = json.loads((HISTORY / "relocations-v1.json").read_text())
    layer = json.loads((HISTORY / "current-source-layer-v1.json").read_text())
    assert moves["schema"] == "lean-hosting-relocations/1"
    assert layer["schema"] == "lean-hosting-current-source-layer/1"
    assert layer["sourceCommit"] == moves["sourceCommit"]
    assert sha((HISTORY / "relocations-v1.json").read_bytes()) == layer["relocationsSHA256"]
    files = layer["files"]
    assert len(files) == len({item["path"] for item in files})
    expected = {item["path"] for item in files}
    excluded = {"target", ".cpcache", "__pycache__"}
    actual = {str(p.relative_to(REPO)) for p in HOSTING.rglob("*")
              if p.is_file() and not excluded.intersection(p.relative_to(HOSTING).parts)
              and p != HISTORY / "current-source-layer-v1.json"}
    assert layer["externalFiles"] == ["bin/run-lean-hosting-research-checks"]
    actual.update(layer["externalFiles"])
    assert actual == expected, (actual - expected, expected - actual)
    for item in files:
        path = relative(item["path"])
        assert not path.is_symlink() and path.is_file(), path
        data = path.read_bytes()
        assert len(data) == item["bytes"] and sha(data) == item["sha256"], path
    changed = {item["original"]: item for item in layer["changedSources"]}
    assert len(changed) == len(layer["changedSources"])
    records = moves["files"] + layer["externalSources"]
    for record, old in historical_blobs(records, moves["sourceCommit"]):
        assert sha(old) == record["sha256"], record["original"]
        current = relative(record["relocated"])
        if record.get("retired"):
            assert not current.exists(), current
            continue
        new = current.read_bytes()
        change = changed.get(record["original"])
        if change is None:
            assert new == old, (record["original"], "Unexplained source mutation")
        else:
            assert sha(new) == change["currentSHA256"]
            expected_bytes = old
            if change["kind"] == "mechanical-replacements":
                for before, after in change["replacements"]:
                    expected_bytes = expected_bytes.replace(before.encode(), after.encode())
            elif change["kind"] == "historical-verifier-wrapper":
                expected_bytes = layer["verifierWrapper"].encode()
            elif change["kind"] == "reviewed-contract-lane-split":
                assert record["original"] == "bin/run-test-contracts"
                expected_bytes = layer["mandatoryCI"].encode()
            else:
                raise AssertionError("Unknown source migration operation")
            assert new == expected_bytes, (record["original"], "Unmapped source edit")
    assert not (REPO / "experiments/lean-ir").exists()
    assert not (REPO / "modules/lean").exists()
    print(json.dumps({"currentFiles": len(files), "exactRelocations": len(moves["files"]),
                      "mechanicallyChangedSources": len(changed),
                      "retiredClosedProbeFiles": len(moves["retirement"]["files"]),
                      "historicalEvidenceVerifiedFromGit": True,
                      "JVMOrNativeExecuted": False, "runtimeAcceptanceClaimed": False}))


if __name__ == "__main__":
    main()
