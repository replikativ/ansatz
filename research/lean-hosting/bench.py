#!/usr/bin/env python3
"""Pinned native Lean and warm JVM microbenchmarks; generated results are ignored."""
import hashlib
from datetime import datetime, timezone
import json
import os
import platform
from pathlib import Path
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "target"
TOOLCHAIN = "leanprover/lean4:v4.33.1"
SOURCES = ["lean/Bench.lean", "src/prototype/bench.clj", "src/prototype/mutable.clj",
           "src/prototype/numeric_compile.clj", "src/prototype/machine.cljc", "fixtures/list-map.jsonl", "bench.py"]

def source_hashes():
    return {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES}

def run(args, **kwargs):
    before = time.perf_counter()
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, **kwargs)
    if result.returncode:
        raise RuntimeError(f"{args!r} failed:\n{result.stdout}\n{result.stderr}")
    return time.perf_counter() - before, result.stdout

def main():
    hashes = source_hashes()
    OUT.mkdir(exist_ok=True)
    _, prefix = run(["lean", f"+{TOOLCHAIN}", "--print-prefix"])
    binpath = Path(prefix.strip()) / "bin"
    env = dict(os.environ, PATH=str(binpath) + os.pathsep + os.environ["PATH"])
    lean_time, _ = run([str(binpath / "lean"), "-c", str(OUT / "Bench.c"), "lean/Bench.lean"], env=env)
    c_time, _ = run([str(binpath / "leanc"), "-O2", str(OUT / "Bench.c"), "-o", str(OUT / "native-bench")], env=env)
    warmup, samples = 20, 11
    native = []
    for workload, size in [("tail", 20000), ("word", 20000), ("unique", 1000), ("shared", 1000)]:
        _, stdout = run([str(OUT / "native-bench"), workload, str(size), str(warmup), str(samples)])
        rows = [tuple(map(int, line.split())) for line in stdout.splitlines()]
        expected = size if workload in ("tail", "word") else 1
        assert len(rows) == samples and all(result == expected for _, result in rows)
        times = [elapsed for elapsed, _ in rows]
        native.append(dict(backend="native-uint64" if workload == "word" else "native",
                           workload="tail" if workload == "word" else workload, size=size, checksum=expected,
                           **{"median-ns": statistics.median(times), "min-ns": min(times),
                              "max-ns": max(times), "raw-ns": times}))
    jvm_time, stdout = run(["clojure", "-Srepro", "-J-Xmx1g", "-M", "-m", "prototype.bench",
                            str(warmup), str(samples)])
    jvm = json.loads(stdout)
    cpu = next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                if line.startswith("model name")), "unknown")
    if hashes != source_hashes():
        raise RuntimeError("Benchmark sources changed during execution; run again")
    result = dict(jvm=jvm, native=native, toolchain=TOOLCHAIN,
                  measured_at=datetime.now(timezone.utc).isoformat(),
                  machine=dict(platform=platform.platform(), cpu=cpu, cpu_count=os.cpu_count()),
                  build_seconds=dict(lean=lean_time, c=c_time), jvm_process_seconds=jvm_time,
                  source_sha256=hashes)
    (OUT / "benchmark.json").write_text(json.dumps(result, indent=2) + "\n")
    for row in jvm["execution"] + [jvm["compiled"]["execution"]] + native:
        print(f'{row["backend"]:10} {row["workload"]:7} n={row["size"]:5} median={row["median-ns"]/1e6:.4f} ms')
    print(f"Full results: {OUT / 'benchmark.json'}")

if __name__ == "__main__":
    main()
