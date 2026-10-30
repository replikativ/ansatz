#!/usr/bin/env python3
"""Verify the pinned computed-data source/vectors; never rewrite goldens.

Check Lean --run and C/native execution against pinned valid-domain vectors.
LEAN_BINARY may select an installed binary reporting the exact source commit.
Compiler temporaries and bounded output files live under the ignored experiment
target/ directory and are removed, including on errors/timeouts. POSIX runner.
"""
import argparse
import hashlib
import json
import os
import pathlib
import resource
import signal
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent
PIN = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
EXE = pathlib.Path(os.environ.get(
    "LEAN_BINARY", pathlib.Path.home() / ".elan/toolchains/leanprover--lean4---v4.33.1/bin/lean"
)).resolve()
MAX_FILE = 512 * 1024 * 1024
MAX_OUTPUT = 64 * 1024


def sha(path, maximum=MAX_FILE):
    assert path.stat().st_size <= maximum, f"file bound exceeded: {path.name}"
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def limits(cpu):
    def apply():
        resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 5))
        resource.setrlimit(resource.RLIMIT_FSIZE, (MAX_FILE, MAX_FILE))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    return apply


def stop_group(process):
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def run(command, label, directory, environment, wall, cpu):
    out = directory / f"{label}.stdout"
    err = directory / f"{label}.stderr"
    with out.open("wb") as stdout, err.open("wb") as stderr:
        process = subprocess.Popen(command, cwd=directory, env=environment,
                                   stdout=stdout, stderr=stderr,
                                   start_new_session=True, preexec_fn=limits(cpu))
        try:
            code = process.wait(timeout=wall)
        except subprocess.TimeoutExpired:
            stop_group(process)
            raise
        if code != 0:
            stop_group(process)
    assert out.stat().st_size <= MAX_OUTPUT and err.stat().st_size <= MAX_OUTPUT, label
    output, errors = out.read_bytes(), err.read_bytes()
    assert code == 0, (label, code, output.decode(errors="replace"), errors.decode(errors="replace"))
    assert not errors, (label, errors.decode(errors="replace"))
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    saved = json.loads((ROOT / "native-receipt.json").read_text())
    assert saved["schema"] == "matching-native-expression-data/1"
    assert saved["lean-commit"] == PIN
    assert sha(ROOT / "DataOracle.lean", MAX_OUTPUT) == saved["source-sha256"], "source pin differs"
    assert sha(ROOT / "native-vectors.json", MAX_OUTPUT) == saved["vectors-sha256"], "vector pin differs"
    vectors = json.loads((ROOT / "native-vectors.json").read_text())
    assert len(vectors) == 160
    arguments = [v["op"] + ":" + ":".join(v["args"]) for v in vectors]
    expected = "".join(v["result"] + "\n" for v in vectors).encode()
    work_root = ROOT.parents[2] / "target/java-expression-data-native"
    work_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="verify-", dir=work_root) as name:
        work = pathlib.Path(name)
        environment = {**os.environ, "LC_ALL": "C", "LANG": "C", "LEAN_NUM_THREADS": "1",
                       "TMPDIR": str(work), "TMP": str(work), "TEMP": str(work)}
        version = run([str(EXE), "--version"], "version", work, environment, 10, 5).decode().strip()
        assert PIN in version, version
        interpreted = run([str(EXE), "--root=" + str(ROOT), "--run", str(ROOT / "DataOracle.lean"), *arguments],
                          "run", work, environment, 40, 30)
        assert interpreted == expected, "--run vectors differ"
        generated, native = work / "DataOracle.c", work / "data-native"
        run([str(EXE), "--root=" + str(ROOT), "-c", str(generated), str(ROOT / "DataOracle.lean")],
            "generate-c", work, environment, 70, 60)
        assert generated.stat().st_size <= 2 * 1024 * 1024
        compiler = EXE.parent / "leanc"
        run([str(compiler), "-Wl,--threads=1", "-o", str(native), str(generated)],
            "compile-native", work, environment, 70, 60)
        compiled = run([str(native), *arguments], "native", work, environment, 30, 15)
        assert compiled == expected, "C/native vectors differ"
        receipt = {
            "schema": "matching-native-expression-data/1", "lean-commit": PIN, "version": version,
            "source-sha256": sha(ROOT / "DataOracle.lean"),
            "vectors-sha256": sha(ROOT / "native-vectors.json"),
            "verifier-sha256": sha(pathlib.Path(__file__).resolve()),
            "binary-sha256": sha(EXE), "runtime-sha256": sha(EXE.parent.parent / "lib/lean/libleanshared.so"),
            "leanc-sha256": sha(compiler), "runtime-archive-sha256": sha(EXE.parent.parent / "lib/lean/libleanrt.a"),
            "generated-c-sha256": sha(generated), "generated-c-bytes": generated.stat().st_size,
            "executable-sha256": sha(native), "executable-bytes": native.stat().st_size,
            "vector-count": len(vectors), "modes": ["--run", "C/native"], "exit": 0, "stderr": "",
            "scope": "Scalar Expr/Level data only; valid Bool, Nat bounds and full UInt64 words; no native panic or AST representation claim.",
            "bounds": {"file-bytes": MAX_FILE, "accepted-stream-bytes": MAX_OUTPUT,
                       "wall-seconds": {"version": 10, "run": 40, "generate-c": 70, "compile-native": 70, "native": 30},
                       "cpu-seconds": {"version": 5, "run": 30, "generate-c": 60, "compile-native": 60, "native": 15},
                       "cpu-hard-grace-seconds": 5, "core-bytes": 0, "address-space-bound": None},
            "environment": {"LEAN_NUM_THREADS": "1", "LC_ALL": "C", "LANG": "C", "linker-threads": 1,
                            "TMPDIR": "repository-local temporary directory"},
            "provenance-scope": "Matching installed binary/runtime, not authentication of the accepted IR checkpoint producer."
        }
        print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
