#!/usr/bin/env python3
"""Record JFR and summarize allocation classes inside compiled guest execution."""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
from bench import ROOT, OUT, run

SOURCES = ["src/prototype/heap_profile.clj", "src/prototype/heap_examples.clj",
           "src/prototype/block_compile.clj", "src/prototype/mutable.clj",
           "src/prototype/machine.cljc", "profile_heap.py"]

def main():
    OUT.mkdir(exist_ok=True)
    hashes = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES}
    recording = OUT / "heap-profile.jfr"
    events_file = OUT / "heap-profile-events.json"
    run(["clojure", "-Srepro", "-J-Xmx1g",
         f"-J-XX:StartFlightRecording=filename={recording},settings=profile,dumponexit=true",
         "-M", "-m", "prototype.heap-profile"])
    with events_file.open("w") as output:
        subprocess.run(["jfr", "print", "--json", "--events", "jdk.ObjectAllocationSample,jdk.ExecutionSample",
                        str(recording)], cwd=ROOT, text=True, stdout=output, check=True)
    types, classes = Counter(), Counter()
    for event in json.loads(events_file.read_text())["recording"]["events"]:
        values = event["values"]
        frames = (values.get("stackTrace") or {}).get("frames", [])
        names = [frame["method"]["type"]["name"].replace("/", ".") for frame in frames]
        if not any("prototype.block_compile$run_BANG_" in name for name in names):
            continue
        types[event["type"]] += 1
        if event["type"] == "jdk.ObjectAllocationSample":
            classes[values["objectClass"]["name"]] += values["weight"]
    assert types["jdk.ObjectAllocationSample"] > 0
    assert hashes == {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES}
    report = dict(workload="200 executions of compiled map on 1000 unique nodes",
                  measured_at=datetime.now(timezone.utc).isoformat(), selected_events=dict(types),
                  allocation_sample_weight_by_class=dict(classes.most_common()),
                  interpretation="Sample weights are not total allocation counts; setup/startup stacks are filtered out. Truncated stacks can be omitted.",
                  source_sha256=hashes,
                  recording_sha256=hashlib.sha256(recording.read_bytes()).hexdigest())
    (OUT / "heap-profile-summary.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(dict(selected_events=dict(types), top_allocation_classes=classes.most_common(6)), indent=2))

if __name__ == "__main__":
    main()
