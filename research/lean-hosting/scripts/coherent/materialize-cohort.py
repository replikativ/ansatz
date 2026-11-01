#!/usr/bin/env python3
"""Capture one committed source cohort; does not compile or run Ansatz/Lean.

Build preparation only. The resulting file hashes are observations, not an
independently accepted consumer contract or a loaded-code attestation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

EXCLUDED = {
    "prototype/finalizer_checkpoint.clj",
    "prototype/full_init_checkpoint_factory.clj",
}
PREFIXES = (
    ("src/", ""),
    ("experiments/lean-ir/src/", ""),
    ("src-java/", "src-java/"),
    ("resources/", ""),
)
MEMO = "experiments/lean-ir/java/prototype/TypedLongMemo.java"


def git(repo, *args):
    return subprocess.run(["git", "-C", str(repo), *args], check=True,
                          stdout=subprocess.PIPE).stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{40}", args.commit):
        parser.error("--commit must be a complete commit ID")
    repo = args.repository.resolve(strict=True)
    if git(repo, "rev-parse", args.commit + "^{commit}").decode().strip() != args.commit:
        parser.error("commit does not resolve exactly")
    output = args.output.resolve()
    if output.exists():
        parser.error("output must be a new directory")
    paths = git(repo, "ls-tree", "-r", "-z", "--name-only", args.commit,
                "--", "src", "src-java", "resources", "experiments/lean-ir/src", MEMO)
    rows = []
    seen = set()
    total = 0
    # Resolve and bound every selected ID before writing anything. Broad source
    # selection avoids guessing a minimal dynamic require/resource closure.
    for raw in paths.split(b"\0"):
        if not raw:
            continue
        original = raw.decode("utf-8", errors="strict")
        if original == MEMO:
            identity = "java/prototype/TypedLongMemo.java"
        else:
            prefix, dest = next((p for p in PREFIXES if original.startswith(p[0])))
            identity = dest + original[len(prefix):]
        if identity in EXCLUDED:
            continue
        if (not re.fullmatch(r"[A-Za-z0-9_./$-]+", identity)
                or any(p in ("", ".", "..") for p in identity.split("/"))):
            raise ValueError("invalid input identity: " + identity)
        if identity in seen:
            raise ValueError("duplicate selected identity: " + identity)
        seen.add(identity)
        if len(seen) > 900:
            raise ValueError("source inventory bound exceeded")
        data = git(repo, "show", args.commit + ":" + original)
        total += len(data)
        if len(data) > 16 * 1024 * 1024 or total > 64 * 1024 * 1024:
            raise ValueError("source capture byte bound exceeded")
        kind = "host-source" if identity.endswith((".clj", ".cljc", ".java")) else "host-resource"
        rows.append(({"id": identity, "kind": kind,
                      "sha256": hashlib.sha256(data).hexdigest(),
                      "source": original, "bytes": len(data)}, data))
    if not rows:
        raise ValueError("empty source inventory")
    output.mkdir(parents=True)
    for row, data in rows:
        target = output / "selected" / row["id"]
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    record = {"schema": "coherent-source-capture/1", "commit": args.commit,
              "status": "SOURCE_CAPTURE_ONLY_NOT_COMPILED_OR_ACCEPTED",
              "bytes": total, "excluded-producer-source-ids": sorted(EXCLUDED),
              "inputs": [row for row, _ in sorted(rows, key=lambda pair: pair[0]["id"])]}
    (output / "source-capture.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"status": record["status"], "files": len(rows), "bytes": total}))


if __name__ == "__main__":
    main()
