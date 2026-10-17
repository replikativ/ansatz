#!/usr/bin/env python3
"""Check the portable DAG bytes without materializing the complete native heap.

Usage: python3 native/check_module_data_transport.py output.jsonl [--hash-artifacts]
This validates the serialized file separately from the native captured-DAG clone
oracle. It never loads native closures or finalizes an Environment.
"""
from array import array
import collections
import hashlib
import json
import pathlib
import re
import sys
import os
import struct

PIN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
MAX_NODES = 25_000_000


def check(path, hash_artifacts=False, publish=None):
    source = pathlib.Path(path)
    descriptor_path = pathlib.Path(publish) if publish else None
    index_path = descriptor_path.with_name(descriptor_path.name + ".index") if publish else None
    staging_path = index_path.with_name(index_path.name + ".partial") if publish else None
    index_digest = hashlib.sha256()
    offsets = array("Q")
    digest = hashlib.sha256()
    tags = collections.Counter()
    layouts = collections.Counter()
    discovered = 0

    def edge(e):
        nonlocal discovered
        assert isinstance(e, dict) and len(e) == 1, ("invalid edge", e)
        if "immediate" in e:
            n = e["immediate"]
            assert isinstance(n, str) and re.fullmatch(r"0|[1-9][0-9]*", n)
            assert 0 <= int(n) < 2**63, ("not a native small scalar payload", n)
        else:
            n = e["ref"]
            assert type(n) is int and 0 <= n < MAX_NODES
            # Native capture discovers IDs in deterministic BFS order. This
            # also rules out disconnected cycles and missing forward targets.
            assert n <= discovered, ("non-BFS/unreachable reference", n, discovered)
            if n == discovered:
                discovered += 1

    with source.open("rb") as f, (staging_path.open("wb") if publish else open(os.devnull, "wb")) as index:
        line = f.readline()
        digest.update(line)
        manifest = json.loads(line)
        assert manifest["kind"] == "manifest"
        assert manifest["input"]["schema"] == "lean-module-data-input/1"
        assert manifest["schema"] == "lean-module-dag/1"
        assert manifest["wordBits"] == 64 and manifest["byteOrder"] == "little"
        assert manifest["immediateEncoding"] == "unsigned-native-tagged-payload"
        assert manifest["input"]["leanCommit"] == PIN
        assert manifest["input"]["leanVersion"] == "4.33.1"
        assert manifest["input"]["nativeEnvironmentFinalized"] is False
        assert manifest["input"]["regionAddressesTransported"] is False
        edge(manifest["root"])
        while True:
            offset = f.tell()
            line = f.readline()
            if not line:
                break
            digest.update(line)
            node = json.loads(line)
            i = len(offsets)
            assert node["id"] == i < discovered
            offsets.append(offset)
            if publish:
                assert line.endswith(b"\n")
                entry = struct.pack(">qI", offset, len(line) - 1) + hashlib.sha256(line[:-1]).digest()
                index.write(entry)
                index_digest.update(entry)
            assert len(offsets) <= MAX_NODES
            tag, kind, fields = node["tag"], node["kind"], node["fields"]
            assert type(tag) is int and isinstance(fields, list)
            for e in fields:
                edge(e)
            tags[str(tag)] += 1
            if kind == "mpz":
                assert tag == 250 and not fields
                assert re.fullmatch(r"0|-?[1-9][0-9]*", node["signedDecimal"])
                assert "bytesHex" not in node
                continue
            data = bytes.fromhex(node["bytesHex"])
            if kind == "ctor":
                assert 0 <= tag <= 243 and len(fields) < 256
                assert node["scalarBytesIncludePadding"] is True
                assert node["objectBytes"] == 8 + 8 * len(fields) + len(data)
                assert len(data) < 1024
                layouts[(tag, len(fields), len(data))] += 1
            elif kind == "array":
                assert tag == 246 and not data
                assert len(fields) == node["size"] <= node["capacity"]
                assert node["objectBytes"] == 24 + 8 * node["capacity"]
            elif kind == "scalar-array":
                assert tag == 248 and not fields
                assert 1 <= node["elementBytes"] <= 255
                assert len(data) == node["size"] * node["elementBytes"]
                assert node["size"] <= node["capacity"]
                assert node["objectBytes"] == 24 + node["capacity"] * node["elementBytes"]
            elif kind == "string":
                assert tag == 249 and not fields and data.endswith(b"\0")
                assert len(data) == node["size"] <= node["capacity"]
                assert node["objectBytes"] == 32 + node["capacity"]
                assert len(data[:-1].decode("utf-8")) == node["utf8Length"]
            else:
                raise AssertionError(("unsupported portable node", kind, tag))
        assert len(offsets) == discovered == manifest["inventory"]["nodes"]
        assert dict(tags) == manifest["inventory"]["tags"]
        assert layouts == collections.Counter({(x["tag"], x["objectFields"], x["scalarBytesWithPadding"]): x["count"]
                                               for x in manifest["inventory"]["constructorLayouts"]})

        @__import__("functools").lru_cache(maxsize=4096)
        def node(i):
            f.seek(offsets[i])
            return json.loads(f.readline())

        def ref(e):
            assert set(e) == {"ref"}
            return node(e["ref"])

        root = ref(manifest["root"])
        assert root["kind"] == "array"
        def name(value):
            parts, seen = [], set()
            while value != {"immediate": "0"}:
                obj = ref(value)
                assert obj["id"] not in seen
                seen.add(obj["id"])
                assert obj["kind"] == "ctor" and obj["tag"] in [1, 2] and len(obj["fields"]) == 2
                parent, part = obj["fields"]
                if obj["tag"] == 1:
                    part = ref(part)
                    assert part["kind"] == "string"
                    parts.append(("str", bytes.fromhex(part["bytesHex"])[:-1].decode("utf-8")))
                else:
                    payload = int(part["immediate"]) if "immediate" in part else int(ref(part)["signedDecimal"])
                    assert payload >= 0
                    parts.append(("num", str(payload)))
                value = parent
            result = ["anonymous"]
            for kind, part in reversed(parts):
                result = [kind, result, part]
            return result

        parts_checked = 0
        artifact_digests = {}
        for module in manifest["input"]["modules"]:
            for part in module["parts"] + module["irParts"]:
                data = ref(root["fields"][part["rootIndex"]])
                assert data["kind"] == "ctor" and data["tag"] == 0 and len(data["fields"]) == 5
                # Exact pinned ModuleData object field order. isModule is in
                # the scalar tail; it must not be guessed from a reference.
                imports, names, constants, extra, entries = map(ref, data["fields"])
                info = part["moduleData"]
                assert all(x["kind"] == "array" for x in [imports, names, constants, extra, entries])
                assert imports["size"] == len(info["imports"])
                for actual, expected in zip(imports["fields"], info["imports"]):
                    imp = ref(actual)
                    assert imp["kind"] == "ctor" and imp["tag"] == 0 and len(imp["fields"]) == 1
                    assert name(imp["fields"][0]) == expected["module"]
                    flags = bytes.fromhex(imp["bytesHex"])[:3]
                    assert list(flags) == [int(expected[k]) for k in ["importAll", "isExported", "isMeta"]]
                assert names["size"] == info["constNamesCount"]
                assert constants["size"] == info["constantCount"]
                assert extra["size"] == info["extraConstNamesCount"]
                assert entries["size"] == len(info["extensions"])
                for entry, expected in zip(entries["fields"], info["extensions"]):
                    pair = ref(entry)
                    assert pair["kind"] == "ctor" and len(pair["fields"]) == 2
                    assert name(pair["fields"][0]) == expected["name"]
                    assert ref(pair["fields"][1])["size"] == expected["entryCount"]
                assert bytes.fromhex(data["bytesHex"])[0] in [0, 1]
                assert bool(bytes.fromhex(data["bytesHex"])[0]) == info["isModule"]
                assert part["artifact"]["oleanVersion"] == 2
                assert part["artifact"]["leanCommit"] == PIN
                if hash_artifacts:
                    file = pathlib.Path(part["artifact"]["filePath"])
                    h = hashlib.sha256()
                    with file.open("rb") as artifact:
                        for chunk in iter(lambda: artifact.read(1024 * 1024), b""):
                            h.update(chunk)
                    artifact_digests[str(file)] = h.hexdigest()
                parts_checked += 1
        if publish:
            index.flush()
            os.fsync(index.fileno())
    result = {"file": str(source), "sha256": digest.hexdigest(), "nodes": len(offsets),
            "partsChecked": parts_checked, "nativeRoundtripVerified": manifest["inventory"]["nativeRoundtripVerified"],
            "artifactSha256": artifact_digests}
    if publish:
        descriptor = {"schema": "lean-module-verified-index/1", "manifest": manifest,
                      "nodes": len(offsets), "sourceBytes": source.stat().st_size,
                      "sourceSha256": result["sha256"], "sourceFile": source.name,
                      "indexFile": index_path.name, "indexBytes": 44 * len(offsets),
                      "indexSha256": index_digest.hexdigest()}
        encoded = (json.dumps(descriptor, sort_keys=True, separators=(",", ":")) + "\n").encode("utf-8")
        temporary = descriptor_path.with_name(descriptor_path.name + ".partial")
        temporary.write_bytes(encoded)
        # Publish data first, descriptor last; only a completed validation run
        # can produce the caller-pinned descriptor capability.
        os.replace(staging_path, index_path)
        os.replace(temporary, descriptor_path)
        result["descriptor"] = str(descriptor_path)
        result["descriptorSha256"] = hashlib.sha256(encoded).hexdigest()
    return result


if __name__ == "__main__":
    args = sys.argv[2:]
    publish = args[args.index("--publish") + 1] if "--publish" in args else None
    print(json.dumps(check(sys.argv[1], "--hash-artifacts" in args, publish=publish), sort_keys=True))
