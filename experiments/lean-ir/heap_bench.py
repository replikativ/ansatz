#!/usr/bin/env python3
"""Compare heap interpreters and generated blocks with pinned native Lean."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import time

from bench import ROOT, OUT, TOOLCHAIN, run

SOURCES = ["lean/HeapProbe.lean", "lean/HeapBench.lean", "src/prototype/heap_bench.clj",
           "src/prototype/heap_examples.clj", "src/prototype/block_compile.clj",
           "src/prototype/mutable.clj", "src/prototype/machine.cljc", "src/prototype/bench.clj",
           "fixtures/list-map.jsonl", "fixtures/list-fold.jsonl", "fixtures/list-reverse.jsonl",
           "fixtures/tree-mirror.jsonl", "heap_bench.py", "bench.py"]

def hashes():
    return {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES}

def main():
    source_hashes = hashes()
    OUT.mkdir(exist_ok=True)
    _, prefix = run(["lean", f"+{TOOLCHAIN}", "--print-prefix"])
    binary = Path(prefix.strip()) / "bin"
    env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], LEAN_PATH=str(OUT))
    before = time.perf_counter()
    run([str(binary / "lean"), "--root=lean", "-o", str(OUT / "HeapProbe.olean"), "-c", str(OUT / "HeapProbe.c"), "lean/HeapProbe.lean"], env=env)
    run([str(binary / "lean"), "--root=lean", "-c", str(OUT / "HeapBench.c"), "lean/HeapBench.lean"], env=env)
    lean_seconds = time.perf_counter() - before
    c_seconds, _ = run([str(binary / "leanc"), "-O2", str(OUT / "HeapProbe.c"), str(OUT / "HeapBench.c"),
                        "-o", str(OUT / "heap-native")], env=env)
    warmup, samples = 20, 11
    native = []
    for workload in ["map", "fold", "reverse", "mirror"]:
        size = 9 if workload == "mirror" else 1000
        expected = {"map": 1, "fold": size * (size - 1) // 2, "reverse": size - 1, "mirror": 2**size - 1}[workload]
        for shared in [False, True]:
            _, stdout = run([str(OUT / "heap-native"), workload, str(size), "shared" if shared else "unique",
                              str(warmup), str(samples)])
            rows = [tuple(map(int, line.split())) for line in stdout.splitlines()]
            assert len(rows) == samples and all(value == expected for _, value in rows)
            times = [elapsed for elapsed, _ in rows]
            native.append(dict(backend="native", workload=workload, size=size, checksum=expected,
                               **{"shared?": shared, "median-ns": statistics.median(times), "raw-ns": times}))
    jvm_seconds, stdout = run(["clojure", "-Srepro", "-J-Xmx1g", "-M", "-m", "prototype.heap-bench",
                               str(warmup), str(samples)])
    jvm = json.loads(stdout)
    if source_hashes != hashes():
        raise RuntimeError("Heap benchmark sources changed during execution")
    cpu = next((line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
                if line.startswith("model name")), "unknown")
    result = dict(jvm=jvm, native=native, toolchain=TOOLCHAIN,
                  measured_at=datetime.now(timezone.utc).isoformat(),
                  machine=dict(platform=platform.platform(), cpu=cpu, cpu_count=os.cpu_count()),
                  build_seconds=dict(lean=lean_seconds, c=c_seconds), jvm_process_seconds=jvm_seconds,
                  source_sha256=source_hashes)
    (OUT / "heap-benchmark.json").write_text(json.dumps(result, indent=2) + "\n")
    for row in jvm["execution"] + native:
        print(f'{row["backend"]:10} {row["workload"]:7} shared={row["shared?"]!s:5} median={row["median-ns"]/1e6:.4f} ms')
    print(f"Full results: {OUT / 'heap-benchmark.json'}")

if __name__ == "__main__":
    main()
