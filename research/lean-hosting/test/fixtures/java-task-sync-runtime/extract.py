#!/usr/bin/env python3
"""Reproduce a bounded original static closure from an accepted read-only CAS.
The caller supplies the independently accepted store and matching SQLite index.
This program verifies each selected raw blob; it does not authenticate a producer.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import sqlite3

INDEX = "74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e"

def key(name):
    return json.dumps(name, separators=(",", ":"), ensure_ascii=False)

def label(name):
    if name[0] == "anonymous":
        return ""
    prefix = label(name[1])
    return (prefix + "." if prefix else "") + str(name[2])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--store", required=True, type=Path)
    parser.add_argument("--index-db", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    directory = Path(__file__).parent
    pending = collections.deque(json.loads((directory / "root-names.json").read_text()))
    selected = {}
    total = 0
    with sqlite3.connect(args.index_db.resolve().as_uri() + "?mode=ro", uri=True) as db:
        metadata = json.loads(db.execute("select json from metadata").fetchone()[0])
        if metadata["index_sha256"] != INDEX:
            raise ValueError("Index cohort differs")
        while pending:
            name = pending.popleft()
            exact = key(name)
            if exact in selected:
                continue
            found = db.execute("select hash from names where name=?", (exact,)).fetchone()
            if found is None:
                raise ValueError("Missing exact Name: " + exact)
            path = args.store / "declarations" / (found[0] + ".json")
            if path.stat().st_size > 1024 * 1024:
                raise ValueError("Individual original row exceeds extraction bound")
            raw = path.read_bytes()
            total += len(raw)
            if len(selected) >= 256 or total > 4 * 1024 * 1024:
                raise ValueError("Static closure exceeds extraction bound")
            if hashlib.sha256(raw).hexdigest() != found[0]:
                raise ValueError("Original CAS blob SHA differs")
            row = json.loads(raw)
            if row["name"] != name:
                raise ValueError("Original Name differs")
            row.pop("pretty", None)
            selected[exact] = {"label": label(name), "sha256": found[0], "row": row}
            pending.extend(row.get("dependencies", []))
    payload = (json.dumps(list(selected.values()), indent=2, ensure_ascii=False) + "\n").encode()
    expected = json.loads((directory / "provenance.json").read_text())
    if hashlib.sha256(payload).hexdigest() != expected["fixture-sha256"]:
        raise ValueError("Reproduced fixture differs from pinned original closure")
    args.output.write_bytes(payload)
    print(json.dumps({"declarations": len(selected), "original-bytes": total,
                      "fixture-sha256": hashlib.sha256(payload).hexdigest()}))

if __name__ == "__main__":
    main()
