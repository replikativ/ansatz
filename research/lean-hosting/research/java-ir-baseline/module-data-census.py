#!/usr/bin/env python3
"""Streaming metadata only: no JVM/native execution or typed-domain admission."""
import collections
import hashlib
import json
import resource
import sys

resource.setrlimit(resource.RLIMIT_AS, (256 * 1024**2, 256 * 1024**2))
path = sys.argv[1]
kinds = collections.Counter()
slots = []
mpz = {}
ref_count = immediate_count = scalar_bytes = maximum_immediate = nodes = 0
digest = hashlib.sha256()
with open(path, "rb") as source:
    first = source.readline(32 * 1024**2 + 1)
    assert len(first) <= 32 * 1024**2
    digest.update(first)
    manifest = json.loads(first)
    assert manifest["schema"] == "lean-module-dag/1"
    assert manifest["input"]["leanCommit"] == "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
    size = len(first)
    for line in source:
        size += len(line)
        assert size <= 32 * 1024**2
        digest.update(line)
        n = json.loads(line)
        assert n["id"] == nodes < 150000
        nodes += 1
        kinds[n["kind"]] += 1
        if n["kind"] == "ctor":
            scalar_bytes += len(n["bytesHex"]) // 2
        if n["kind"] == "mpz":
            mpz[n["id"]] = {"decimal": n["signedDecimal"], "uses": []}
        for index, edge in enumerate(n["fields"]):
            if "immediate" in edge:
                immediate_count += 1
                value = int(edge["immediate"])
                assert 0 <= value <= 2**63 - 1
                maximum_immediate = max(maximum_immediate, value)
                if value > 2**31 - 1:
                    slots.append([n["id"], index, edge["immediate"]])
            else:
                ref_count += 1
assert nodes == manifest["inventory"]["nodes"]
with open(path, "rb") as source:
    next(source)
    for line in source:
        n = json.loads(line)
        for index, edge in enumerate(n["fields"]):
            if edge.get("ref") in mpz:
                mpz[edge["ref"]]["uses"].append([n["id"], index])
print(json.dumps({"schema": "module-data-java-normalization-census/1",
                  "sha256": digest.hexdigest(), "source_bytes": size,
                  "source_nodes": nodes, "source_kinds": kinds,
                  "normalized_nodes": kinds["ctor"] + kinds["array"],
                  "constructor_scalar_bytes_including_padding": scalar_bytes,
                  "serialized_field_references": ref_count,
                  "serialized_field_immediates": immediate_count,
                  "manifest_occurrences": {k: manifest["inventory"][k] for k in
                                           ("referenceOccurrences", "immediateOccurrences")},
                  "maximum_immediate": maximum_immediate,
                  "ambiguous_immediate_slots": slots, "mpz": mpz,
                  "typed_domain_status": "unproven; physical tags are not typed-use evidence"},
                 indent=2))
