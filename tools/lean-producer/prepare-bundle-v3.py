#!/usr/bin/env python3
"""Prepare private bundle/2 metadata ONLY; never copy binaries, archive or publish.

The expected reviewed build receipt digest is mandatory. Output correspondence
is descriptive; this tool never registers an SDK producer or issues a compiler.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat

COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
BINARY = "9cf560924d662f4078be81322ef00d25f6ec71bb475faffa183b5c8a766f5004"
MODULES = ("NativeEntryTransport", "NativeTypeGraph", "NativeNominalEntryEvidence")
AUXILIARY = {
    "startupHeader": {("f8c92d652c596b9bf656135348b190a5c09cf61ec40c8775835cf180a8833dd1", "2693f971452aa28190ca5c1033bf2b1030f9703b22f53181cd0591b1ab90399c")},
    "typedSource": {("a48e00225fe08c1a74b66fff1102fd0c11ecefaaafc20ddcf6e28aaf363c99d3", "83342c9582dd43aef3974ffadb6f989c1f7bd23d66b3c406258ca31223030041"),
                    ("ac6ec4462614d39beed124c81f304b3c4875ce5fc6b15fd7b31bd0bbd56ca190", "c28866c7fcf13b141336547d4da1372ad1f90dfe46c04e5f72e5081466ce2d36")},
}


def canonical(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def child(root, relative):
    if not isinstance(relative, str) or not 1 <= len(relative) <= 1024 or "\\" in relative:
        raise ValueError("Bounded relative path required")
    parts = relative.split("/")
    if any(part in ("", ".", "..") for part in parts) or Path(relative).is_absolute():
        raise ValueError("Noncanonical relative path")
    path = root
    for part in parts:
        path = path / part
        if path.is_symlink():
            raise ValueError("Symlink in candidate input")
    if not path.is_file() or path.resolve() != path:
        raise ValueError("Regular contained input required")
    return path


def record(path, maximum):
    before = path.stat(follow_symlinks=False)
    if not stat.S_ISREG(before.st_mode) or before.st_size > maximum:
        raise ValueError("Input extent/type bound")
    h = hashlib.sha256()
    total = 0
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(65536), b""):
            total += len(chunk)
            if total > maximum:
                raise ValueError("Input grew past extent bound")
            h.update(chunk)
    after = path.stat(follow_symlinks=False)
    fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
    if any(getattr(before, key) != getattr(after, key) for key in fields):
        raise ValueError("Input changed while hashing")
    return {"bytes": before.st_size, "sha256": h.hexdigest()}


def pairs(items):
    out = {}
    for key, value in items:
        if key in out:
            raise ValueError("Duplicate JSON key")
        out[key] = value
    return out


def read_json(path, maximum):
    before = record(path, maximum)
    with path.open("rb") as source:
        data = source.read(maximum + 1)
    if len(data) > maximum or digest(data) != before["sha256"] or record(path, maximum) != before:
        raise ValueError("Metadata changed during bounded read")
    return json.loads(data.decode("utf-8"), object_pairs_hook=pairs)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--entry-build", required=True, type=Path)
    p.add_argument("--reviewed-receipt-sha256", required=True)
    p.add_argument("--legacy-bundle", required=True, type=Path)
    p.add_argument("--source-root", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path, help="New metadata-only directory")
    a = p.parse_args()
    build = a.entry_build.resolve(strict=True)
    legacy = a.legacy_bundle.resolve(strict=True)
    source_root = a.source_root.resolve(strict=True)
    receipt_path = child(build, "candidate-receipt.json")
    receipt_record = record(receipt_path, 2 * 1048576)
    if receipt_record["sha256"] != a.reviewed_receipt_sha256:
        raise ValueError("Build receipt differs from explicit reviewed identity")
    r = read_json(receipt_path, 2 * 1048576)
    rows = r["sourceClosure"]
    if r["schema"] != "lean-native-entry-candidate/1" or r["status"] != "entry-built-not-published" or r["leanCommit"] != COMMIT:
        raise ValueError("Wrong completed native build profile")
    if len(rows) != 3 or r["sourceClosureSHA256"] != digest(canonical(rows)):
        raise ValueError("Native builder source closure digest mismatch")
    mappings = []
    captured = []

    def bind(source, destination, maximum, expected):
        got = record(source, maximum)
        if got["sha256"] != expected:
            raise ValueError("Input differs from reviewed build/pair: " + str(source))
        captured.append((source, maximum, got))
        mappings.append({"source": str(source), "destination": destination, **got})
        return got

    for row, module in zip(rows, MODULES):
        if set(row) != {"module", "source", "sha256"} or row["module"] != ["str", ["anonymous"], module] or row["source"] != module + ".lean":
            raise ValueError("Exact maintained source dependency order required")
        bind(child(build, row["source"]), row["source"], 2 * 1048576, row["sha256"])
        if record(child(source_root, "tools/lean-producer/src/" + row["source"]), 2 * 1048576)["sha256"] != row["sha256"]:
            raise ValueError("Current maintained source differs from compiled snapshot")
    binary = child(build, "entry")
    bind(binary, "bin/entry", 256 * 1048576, BINARY)
    if not os.access(binary, os.X_OK):
        raise ValueError("Candidate executable permission missing")
    products = r["products"]
    if not isinstance(products, list) or not 1 <= len(products) <= 32 or len({x["path"] for x in products}) != len(products):
        raise ValueError("Bounded unique compiled products required")
    if next(x for x in products if x["path"] == "entry") != {"path": "entry", **record(binary, 256 * 1048576)}:
        raise ValueError("Receipt does not bind executable bytes")
    for product in products:
        path = child(build, product["path"])
        if record(path, 256 * 1048576 if product["path"] == "entry" else 64 * 1048576) != {k: product[k] for k in ("bytes", "sha256")}:
            raise ValueError("Compiled product changed")
    expected_link = {"supportInterpreter": True, "interpreterExportFlag": "-rdynamic", "linkerThreads": 1, "authority": "pinned Lake.Config.LeanExe.exeOnlyLinkArgs"}
    links = [x for x in r["processes"] if x["label"] == "link-entry"]
    if r.get("standaloneLinkConfig") != expected_link or len(links) != 1 or links[0].get("exit") != 0:
        raise ValueError("Successful official interpreter link required")
    bind(receipt_path, "receipts/entry-build.json", 2 * 1048576, receipt_record["sha256"])
    old = read_json(child(legacy, "producer-bundle.json"), 262144)
    producers = {}
    for name in AUXILIARY:
        desc = old["producers"][name]
        if set(desc) != {"source", "sourceSHA256", "binary", "binarySHA256"} or (desc["sourceSHA256"], desc["binarySHA256"]) not in AUXILIARY[name]:
            raise ValueError("Unchanged independently admitted auxiliary pair required")
        bind(child(legacy, desc["source"]), desc["source"], 2 * 1048576, desc["sourceSHA256"])
        bind(child(legacy, desc["binary"]), desc["binary"], 256 * 1048576, desc["binarySHA256"])
        producers[name] = desc
    entry = {"binary": "bin/entry", "binarySHA256": BINARY, "source": MODULES[-1] + ".lean", "sourceSHA256": rows[-1]["sha256"], "sourceClosure": rows, "sourceClosureSHA256": r["sourceClosureSHA256"], "buildReceipt": "receipts/entry-build.json", "buildReceiptSHA256": receipt_record["sha256"]}
    producers["entry"] = entry
    manifest = {"schema": "lean-native-producer-bundle/2", "leanCommit": COMMIT, "leanVersion": "4.33.1", "target": "x86_64-unknown-linux-gnu", "wordBits": 64, "producers": producers}
    expected = {key: entry[key] for key in ("binarySHA256", "sourceSHA256", "sourceClosureSHA256", "buildReceiptSHA256")}
    destinations = [x["destination"] for x in mappings]
    identities = [(path.stat().st_dev, path.stat().st_ino) for path, _, _ in captured]
    if len(set(destinations)) != len(destinations) or len(set(identities)) != len(identities):
        raise ValueError("Bundle roles must not alias")
    for path, maximum, before in captured:
        if record(path, maximum) != before:
            raise ValueError("Input changed before metadata output")
    a.output.mkdir(parents=True, exist_ok=False)
    for name, value in [("producer-bundle.json", manifest), ("expected-identities.json", expected), ("staging-plan.json", {"scope": "metadata-only-no-copy-no-publication", "admission": False, "preparerSHA256": record(Path(__file__).resolve(), 2 * 1048576)["sha256"], "nativeBuildReceiptSHA256": receipt_record["sha256"], "files": mappings})]:
        (a.output / name).write_bytes(canonical(value) + b"\n")
    print("Candidate metadata only:", a.output)


if __name__ == "__main__":
    main()
