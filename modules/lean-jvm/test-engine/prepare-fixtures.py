#!/usr/bin/env python3
"""Materialize verified engine test data into a fresh, caller-owned directory."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys
import zipfile


def materialize(destination):
    source = Path(__file__).resolve().parent
    destination = Path(destination).resolve()
    destination.mkdir(parents=True, exist_ok=True)
    if any(destination.iterdir()):
        raise ValueError("Fixture destination must be empty")
    index = json.loads((source / "fixture-index.json").read_text())
    if index["schema"] != "engine-fixture-corpus/1":
        raise ValueError("Unsupported fixture index")
    expected = {entry["path"]: entry for entry in index["files"]}
    if len(expected) != len(index["files"]):
        raise ValueError("Duplicate fixture index path")
    with zipfile.ZipFile(source / "corpus.zip") as archive:
        names = archive.namelist()
        if len(names) != len(set(names)) or set(names) != set(expected):
            raise ValueError("Fixture archive/index mismatch")
        for name in names:
            path = PurePosixPath(name)
            if path.is_absolute() or ".." in path.parts or "\\" in name:
                raise ValueError("Invalid fixture path")
            data = archive.read(name)
            entry = expected[name]
            if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
                raise ValueError("Fixture digest mismatch: " + name)
            target = destination.joinpath(*path.parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    return len(expected)


if __name__ == "__main__":
    print("Verified and materialized", materialize(sys.argv[1]), "engine fixtures")
