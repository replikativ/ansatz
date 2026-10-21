#!/usr/bin/env python3
"""Collect source-time local initialization plans using the pinned exporter.

Run from any directory: python3 scripts/collect-init-plans.py Lean.Parser.Module Init
Multiple roots collect the union of their source import graphs. Existing cached
module bundles remain valid when adding a root; fingerprints are per module.
The exporter must already exist at target/lean-ir-export. This script does not
build or change Lean/exporter sources. Cache stamps cover source and exporter
SHA256; validated output hashes permit inexpensive subsequent integrity checks.
An exclusive OS lock allows one collector per output cache; competing launches
fail immediately instead of racing shared temporary files or collection metadata.
"""

import argparse
import concurrent.futures
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


TOOLCHAIN = "+leanprover/lean4:v4.33.1"
VERSION = "4.33.1"
BASE = Path(__file__).resolve().parent.parent
PRIMITIVE_DECODER = json.JSONDecoder()


def iterative_json(text):
    """Decode deep producer JSON without raising Python's recursion limit.

    Only primitive tokens use the standard decoder; containers use an explicit
    stack. Unlike a high recursion-limit C decoder, deep FnBodies cannot exhaust
    the native stack. This fallback is safe in concurrent collector workers.
    """
    frames, root, root_set, position = [], None, False, 0

    def error(message):
        raise json.JSONDecodeError(message, text, position)

    def attach(value):
        nonlocal root, root_set
        if not frames:
            root, root_set = value, True
        else:
            frame = frames[-1]
            if frame[0] == "array":
                frame[1].append(value)
            else:
                frame[1][frame[3]] = value
                frame[3] = None
            frame[2] = "comma"

    while True:
        while position < len(text) and text[position] in " \t\r\n":
            position += 1
        if not frames and root_set:
            if position != len(text):
                error("Extra data")
            return root
        if position == len(text):
            error("Unexpected end of JSON")
        char = text[position]
        if frames:
            frame = frames[-1]
            kind, _, state, _ = frame
            closing = "]" if kind == "array" else "}"
            if state == "comma":
                if char == closing:
                    frames.pop()
                    position += 1
                    continue
                if char != ",":
                    error("Expected comma or container end")
                frame[2] = "value" if kind == "array" else "key"
                position += 1
                continue
            if state in ("key", "key-or-end"):
                if state == "key-or-end" and char == "}":
                    frames.pop()
                    position += 1
                    continue
                if char != '"':
                    error("Expected object key")
                frame[3], position = PRIMITIVE_DECODER.raw_decode(text, position)
                frame[2] = "colon"
                continue
            if state == "colon":
                if char != ":":
                    error("Expected colon")
                frame[2] = "value"
                position += 1
                continue
            if state == "value-or-end" and char == "]":
                frames.pop()
                position += 1
                continue
        if char in "[{":
            value = [] if char == "[" else {}
            attach(value)
            frames.append(["array" if char == "[" else "object", value,
                           "value-or-end" if char == "[" else "key-or-end", None])
            position += 1
        else:
            value, position = PRIMITIVE_DECODER.raw_decode(text, position)
            attach(value)


def parse_row(line):
    try:
        return json.loads(line)
    except RecursionError:
        return iterative_json(line)


def label(name):
    parts = []
    while name and name[0] != "anonymous":
        if len(name) != 3 or name[0] not in ("str", "num"):
            raise ValueError("Malformed structured Lean name")
        parts.append(str(name[2]))
        name = name[1]
    if name != ["anonymous"]:
        raise ValueError("Malformed Lean name terminator")
    return ".".join(reversed(parts))


def atomic_json(path, value):
    temp = path.with_name(path.name + ".tmp")
    temp.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    temp.replace(path)


def validate_manifest(manifest, module):
    plan = manifest.get("initializationPlan")
    if (manifest.get("kind") != "manifest" or manifest.get("schema") != "lean-ir-probe/1"
            or manifest.get("leanVersion") != VERSION or not plan
            or plan.get("schema") != "lean-init-plan/1" or label(plan["module"]) != module):
        raise ValueError(f"Invalid producer manifest for {module}")
    return plan


def validate_output(path, module):
    digest, count = hashlib.sha256(), 0
    with path.open("rb") as stream:
        first = next(stream)
        digest.update(first)
        manifest = parse_row(first.decode("utf-8"))
        validate_manifest(manifest, module)
        for raw in stream:
            digest.update(raw)
            row = parse_row(raw.decode("utf-8"))
            if row.get("kind") != "decl" or row.get("sourceLocal") is not True:
                raise ValueError(f"Invalid local declaration in {module}, row {count + 2}")
            count += 1
    return manifest, count, digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("roots", nargs="*", default=["Lean.Parser.Module"])
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--output", type=Path, default=BASE / "target/module-plans")
    parser.add_argument("--exporter", type=Path, default=BASE / "target/lean-ir-export")
    args = parser.parse_args()
    roots = list(dict.fromkeys(args.roots or ["Lean.Parser.Module"]))
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    output, exporter = args.output.resolve(), args.exporter.resolve()
    output.mkdir(parents=True, exist_ok=True)
    # Keep this descriptor alive for the whole main call, including exporter
    # children and metadata publication. A surviving collector child must keep
    # ownership when its launching shell is interrupted. Never unlink the lock:
    # concurrent processes must flock the same inode.
    collector_lock = (output / "collector.lock").open("a")
    try:
        fcntl.flock(collector_lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        parser.error(f"Another initialization-plan collector owns cache: {output}")
    prefix = Path(subprocess.check_output(["lean", TOOLCHAIN, "--print-prefix"], text=True).strip())
    source_root = prefix / "src/lean"
    exporter_hash = hashlib.sha256(exporter.read_bytes()).hexdigest()
    environment = dict(os.environ, LEAN_SYSROOT=str(prefix))
    started = time.monotonic()

    def produce(module):
        source = source_root / (module.replace(".", "/") + ".lean")
        fingerprint = {"source-sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                       "exporter-sha256": exporter_hash, "toolchain": VERSION}
        path, stamp = output / (module + ".jsonl"), output / (module + ".stamp.json")
        cached = json.loads(stamp.read_text()) if stamp.exists() else {}
        cached_fingerprint = cached.get("fingerprint", cached)  # legacy collector stamps
        if path.exists() and cached_fingerprint == fingerprint:
            if cached.get("output-sha256"):
                digest = hashlib.sha256()
                with path.open("rb") as stream:
                    first = next(stream)
                    digest.update(first)
                    manifest = parse_row(first.decode("utf-8"))
                    validate_manifest(manifest, module)
                    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                        digest.update(chunk)
                if digest.hexdigest() != cached["output-sha256"]:
                    raise ValueError(f"Cached producer output digest mismatch: {module}")
                count = cached["declarations"]
            else:
                manifest, count, digest = validate_output(path, module)
                atomic_json(stamp, {"fingerprint": fingerprint, "output-sha256": digest, "declarations": count})
        else:
            temp = path.with_name(path.name + ".tmp")
            with temp.open("wb") as stream:
                result = subprocess.run([str(exporter), "--source", str(source), "--local", module],
                                        stdout=stream, stderr=subprocess.PIPE, env=environment, cwd=BASE)
            if result.returncode:
                raise RuntimeError(f"{module}: {result.stderr.decode(errors='replace')}")
            manifest, count, digest = validate_output(temp, module)
            temp.replace(path)
            atomic_json(stamp, {"fingerprint": fingerprint, "output-sha256": digest, "declarations": count})
        plan = manifest["initializationPlan"]
        imports = [label(item["module"] if isinstance(item, dict) else item) for item in plan["imports"]]
        return imports, {"actions": len(plan["actions"]), "declarations": count}

    pending, seen, done, active = list(reversed(roots)), set(), {}, {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or active:
            while pending and len(active) < args.jobs:
                module = pending.pop()
                if module not in seen:
                    seen.add(module)
                    active[pool.submit(produce, module)] = module
            if not active:
                continue
            ready, _ = concurrent.futures.wait(active, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in ready:
                module = active.pop(future)
                try:
                    imports, stats = future.result()
                except Exception as error:
                    print(json.dumps({"error": str(error), "module": module}), flush=True)
                    raise
                done[module] = stats
                pending.extend(imports)
                print(json.dumps({"module": module, "done": len(done), "discovered": len(seen), **stats,
                                  "elapsed": round(time.monotonic() - started, 2)}), flush=True)
    atomic_json(output / "collection.json", {"root": roots[0], "roots": roots, "modules": done,
                "exporter-sha256": exporter_hash, "elapsed": time.monotonic() - started})


if __name__ == "__main__":
    main()
