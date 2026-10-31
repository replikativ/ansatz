#!/usr/bin/env python3
"""Verify pinned oracle source/golden and optionally a new native stdout file.
This script never executes a compiler and never rewrites its own goldens.
"""
import argparse
import hashlib
from pathlib import Path
SOURCE = "f127e506f03546a1a69293cb9dd5a0061d971e1694dcde9eccee2757e9bbfa23"
STDOUT = "10b0cecbbe7b456c90d51da1cbc116d644da720f350910664cbe76b0d0f7d7c4"
def checked(path, expected):
    if path.stat().st_size > 65536:
        raise SystemExit("Oracle file exceeds 64KiB bound: " + str(path))
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise SystemExit("Oracle hash differs: " + str(path))
    return data
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, help="newly observed stdout to compare")
args = parser.parse_args()
root = Path(__file__).resolve().parent
checked(root / "FoldConstsOracle.lean", SOURCE)
golden = checked(root / "native.stdout", STDOUT)
if args.output and checked(args.output, STDOUT) != golden:
    raise SystemExit("Oracle bytes differ")
print("Pinned FoldConsts oracle source/stdout verified")
