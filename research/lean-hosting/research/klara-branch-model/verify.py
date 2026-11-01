#!/usr/bin/env python3
"""Check elementary proofs, audit their axioms, and validate runnable samples.

LEAN_BIN must name an already installed native Lean executable. No dependency
fetch, Lake build, JVM, host callback, or frontend image is invoked.
"""
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "BranchModel.lean"
LEAN = os.environ.get("LEAN_BIN", "lean")


def run(*args, source=None):
    result = subprocess.run(
        [LEAN, *args], input=source, text=True, capture_output=True, check=True,
        cwd=ROOT,
    )
    if result.stderr:
        raise AssertionError(result.stderr)
    return result.stdout


version = run("--version").strip()
text = SOURCE.read_text()
assert not re.search(r"\b(sorry|axiom|admit)\b", text)
theorems = re.findall(r"^theorem (\w+)", text, re.MULTILINE)
audit = run("--stdin", source=text + "\n" + "\n".join(
    f"#print axioms KlaraBranchModel.{name}" for name in theorems
))
for name in theorems:
    assert f"'KlaraBranchModel.{name}' does not depend on any axioms" in audit, audit

output = run("--run", str(SOURCE))
rows = [json.loads(line) for line in output.splitlines()]
assert len(rows) == 28
assert len({(r["base"], r["left"], r["right"]) for r in rows[:-1]}) == 27
for row in rows[:-1]:
    b, l, r = row["base"], row["left"], row["right"]
    assert row["kind"] == "store"
    assert row["observations"] == [b, l, l, r, r, b, b]
assert rows[-1] == {
    "kind": "authority", "secondChoiceRejected": True,
    "completeAttempts": 2, "completeReceipts": 2,
    "completeReplayRejected": True, "incompleteAttempts": 2,
    "incompleteReceipts": 1, "incompleteReplayRejected": True,
    "incompleteChoiceRejected": True,
}
(ROOT / "sample-results.jsonl").write_text(output)
print(version)
print(f"PASS: {len(theorems)} named theorems checked; all have no axioms")
print("PASS: 27 store observations and 1 authority observation")
print("Wrote sample-results.jsonl (bounded executable reference, not runtime refinement)")
