#!/usr/bin/env python3
"""Verify the pinned synchronous-task source/trace; never rewrite goldens.

Default: check Lean --run and C/native execution. --run-only skips compilation.
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
CASES = ["nested-sync-lifo-depth-first", "duplicate-losing-token-release",
         "discarded-baseio-keepalive", "pure-waiting-capture-drop",
         "drop-later-detached-dependent", "cancel-finish-and-inline-scope"]


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
    parser.add_argument("--run-only", action="store_true", help="verify --run only, without C compilation")
    args = parser.parse_args()
    saved = json.loads((ROOT / "sync-native-receipt.json").read_text())
    assert saved["schema"] == "matching-native-sync-task-oracle/1"
    assert saved["lean-commit"] == PIN
    assert sha(ROOT / "SyncOracle.lean", MAX_OUTPUT) == saved["source-sha256"], "source pin differs"
    assert sha(ROOT / "sync-native-output.txt", MAX_OUTPUT) == saved["output-sha256"], "golden pin differs"
    expected = (ROOT / "sync-native-output.txt").read_bytes()
    work_root = ROOT.parents[2] / "target/java-sync-task-oracles"
    work_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="verify-", dir=work_root) as name:
        work = pathlib.Path(name)
        environment = {**os.environ, "LC_ALL": "C", "LANG": "C", "LEAN_NUM_THREADS": "1",
                       "TMPDIR": str(work), "TMP": str(work), "TEMP": str(work)}
        version = run([str(EXE), "--version"], "version", work, environment, 10, 5).decode().strip()
        assert PIN in version, version
        interpreted = run([str(EXE), "--root=" + str(ROOT), "--run", str(ROOT / "SyncOracle.lean")],
                          "run", work, environment, 40, 30)
        assert interpreted == expected, ("--run trace differs", interpreted.decode(errors="replace"))
        receipt = {
            "schema": "matching-native-sync-task-oracle/1", "lean-commit": PIN,
            "version": version, "binary-sha256": sha(EXE),
            "runtime-sha256": sha(EXE.parent.parent / "lib/lean/libleanshared.so"),
            "source-sha256": sha(ROOT / "SyncOracle.lean"),
            "output-sha256": sha(ROOT / "sync-native-output.txt"),
            "verifier-sha256": sha(pathlib.Path(__file__).resolve()),
            "cases": CASES, "modes": ["--run"], "exit": 0, "stderr": "",
            "environment": {"LC_ALL": "C", "LANG": "C", "LEAN_NUM_THREADS": "1",
                            "TMPDIR": "repository-local temporary directory"},
            "bounds": {"file-bytes": MAX_FILE, "output-bytes-per-command": MAX_OUTPUT,
                       "version-wall-seconds": 10, "run-wall-seconds": 40,
                       "compile-wall-seconds-per-command": 70, "native-wall-seconds": 30,
                       "version-cpu-seconds": 5, "run-cpu-seconds": 30,
                       "compile-cpu-seconds-per-command": 60, "native-cpu-seconds": 15,
                       "cpu-hard-grace-seconds": 5, "core-bytes": 0,
                       "address-space-bound": None},
            "scope": "Deterministic synchronous ownership/cancellation observations, not JVM pending-task support or native timing.",
            "provenance-scope": "Matching installed binary/runtime; not authentication of the accepted IR checkpoint producer."
        }
        if not args.run_only:
            generated, native = work / "SyncOracle.c", work / "sync-native"
            run([str(EXE), "--root=" + str(ROOT), "-c", str(generated), str(ROOT / "SyncOracle.lean")],
                "generate-c", work, environment, 70, 60)
            assert generated.stat().st_size <= 2 * 1024 * 1024, "generated C bound"
            compiler = EXE.parent / "leanc"
            run([str(compiler), "-Wl,--threads=1", "-o", str(native), str(generated)],
                "compile-native", work, environment, 70, 60)
            compiled = run([str(native)], "native", work, environment, 30, 15)
            assert compiled == expected, ("C/native trace differs", compiled.decode(errors="replace"))
            receipt["modes"].append("C/native")
            receipt["aot"] = {
                "exit": 0, "stderr": "", "matches-run-trace": True,
                "leanc-sha256": sha(compiler), "linker-threads": 1,
                "generated-c-sha256": sha(generated), "generated-c-bytes": generated.stat().st_size,
                "executable-sha256": sha(native), "executable-bytes": native.stat().st_size,
                "runtime-archive-sha256": sha(EXE.parent.parent / "lib/lean/libleanrt.a")
            }
        print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
