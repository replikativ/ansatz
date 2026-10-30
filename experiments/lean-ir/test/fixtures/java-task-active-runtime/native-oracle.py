#!/usr/bin/env python3
"""Verify the checked native trace; emit a receipt without rewriting goldens.

LEAN_BINARY may select a matching installed Lean. This is a native reference
probe, not a JVM memory measurement or part of normal Ansatz loading.
"""
import argparse
import hashlib
import json
import os
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent
PIN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
EXE = pathlib.Path(os.environ.get(
    "LEAN_BINARY", pathlib.Path.home() / ".elan/toolchains/leanprover--lean4---v4.33.1/bin/lean"
)).resolve()


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


env = {**os.environ, "LC_ALL": "C", "LANG": "C"}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--aot", action="store_true", help="also verify generated C/native execution")
args = parser.parse_args()
version = subprocess.run([str(EXE), "--version"], env=env, capture_output=True,
                         check=True, timeout=10, text=True).stdout.strip()
assert PIN in version, version
expected = (ROOT / "native-output.txt").read_bytes()
result = subprocess.run([str(EXE), "--run", str(ROOT / "Oracle.lean")],
                        env=env, capture_output=True, timeout=30)
assert result.returncode == 0, result.stderr.decode(errors="replace")
assert not result.stderr, result.stderr
assert result.stdout == expected, result.stdout.decode(errors="replace")
runtime = EXE.parent.parent / "lib/lean/libleanshared.so"
receipt = {
    "schema": "matching-native-task-order-oracle/1", "lean-commit": PIN,
    "version": version, "binary-sha256": sha(EXE),
    "runtime-sha256": sha(runtime), "script-sha256": sha(ROOT / "Oracle.lean"),
    "output-sha256": sha(ROOT / "native-output.txt"), "exit": result.returncode,
    "stderr": "", "environment": {"LC_ALL": "C", "LANG": "C"},
    "mode": "--run", "scope": "Deterministic promise lifecycle and synchronous callback trace; no async timing or JVM implementation claim.",
    "provenance-scope": "Matching installed binary/runtime, not proof this executable produced the accepted IR checkpoint."
}
if args.aot:
    compiler = EXE.parent / "leanc"
    with tempfile.TemporaryDirectory(prefix="lean-task-oracle-") as directory:
        generated = pathlib.Path(directory) / "Oracle.c"
        native = pathlib.Path(directory) / "oracle-native"
        for command in ([str(EXE), "-c", str(generated), str(ROOT / "Oracle.lean")],
                        [str(compiler), "-o", str(native), str(generated)]):
            built = subprocess.run(command, env=env, capture_output=True, timeout=60)
            assert built.returncode == 0, (built.stdout, built.stderr)
        compiled = subprocess.run([str(native)], env=env, capture_output=True, timeout=30)
        assert compiled.returncode == 0 and not compiled.stderr, compiled.stderr
        assert compiled.stdout == expected, compiled.stdout.decode(errors="replace")
        receipt["aot"] = {"exit": 0, "stderr": "", "matches-run-trace": True,
                          "leanc-sha256": sha(compiler), "generated-c-sha256": sha(generated),
                          "executable-sha256": sha(native)}
print(json.dumps(receipt, indent=2))
