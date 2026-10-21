# Net-zero heap-overlay dirtiness

`HeapOverlay.remove` now cancels a dirty key when successful removal restores its
original Java-map absence and the base is still visible. Original base entries,
including null values, keep deletion evidence. After `clear`, deletion tracking
remains conservative. The change preserves Map results, reference counts,
monotone reference IDs and retained snapshots.

Previously, each allocation followed by release left its historical ID in the
dirty set until the mutable operation ended. Enough such IDs selected the full
heap reconstruction path even when the effective heap had no changes. The
candidate keeps that set empty and lets freeze return the exact retained base.
HashMap/HashSet capacity may still retain peak simultaneous occupancy.

The [measurement](../measurements/heap-overlay-net-dirty.json) records 31 tests /
664 assertions and five paired samples. Each sample uses a retained 16,384-node
base and 32,768 actual mutable constructor/release pairs. The historical overlay
rebuilt the heap; the candidate reused the exact base in every sample. Median
freeze allocation was 3,067,736 versus 25,368 current-thread allocated bytes. This
micro workload does not establish frontend latency, campaign retained-byte
reduction or the dominant cause of campaign GC. The composed comprehensive
runtime gate passed 934 tests / 91,679 assertions on the current reconstruction
source tree with only the candidate Java class and changed heap test overlaid.

The benchmark compares both Java classes inside one isolated JVM and alternates
sample order. Its historical class comes from the exact baseline commit, with
only the class identifier renamed. Every sample checks heap equality, next-ID and
allocation-stat changes, and execution through the retained original and frozen
snapshots. The focused tests also check real surviving allocations, changed and
deleted original nodes, Java-distinct numeric keys, null values and `clear`.

For reproduction, first prepare the repository's usual compiled Java classes.
From `experiments/lean-ir`, create the exact historical input:

```sh
python3 - <<'PY'
from pathlib import Path
import hashlib, subprocess
out = Path('target/heap-net-dirty')
out.mkdir(parents=True, exist_ok=True)
(out / 'classes').mkdir(exist_ok=True)
source = subprocess.check_output([
    'git', 'show',
    'f6b2bf5d443d022be66bc030a581d9a6020a57cf:src-java/ansatz/runtime/HeapOverlay.java'
]).decode()
assert hashlib.sha256(source.encode()).hexdigest() == 'bb33de6a4710bb7f80700fc4a65cbbc82c76a489924d1d498603e2a253adf7e7'
(out / 'HistoricalHeapOverlay.java').write_text(source.replace('HeapOverlay', 'HistoricalHeapOverlay'))
PY
```

Run compilation and the benchmark sequentially under the campaign resource guard
(the observed run used a 512 MiB test heap, 1024 MiB combined RSS ceiling,
180-second deadline and 2 GiB available-memory floor):

```sh
javac -J-Xmx128m -cp "$(clojure -Spath)" -d target/heap-net-dirty/classes ../../src-java/ansatz/runtime/HeapOverlay.java target/heap-net-dirty/HistoricalHeapOverlay.java
clojure -J-Xmx512m -Sdeps '{:paths ["target/heap-net-dirty/classes" "src" "test"]}' -M scripts/benchmark-heap-net-dirty.clj
```

Keep the isolated class directory first on the classpath. Raw paired samples are
written to `target/heap-net-dirty-benchmark.json`; the tracked receipt preserves
the original observed pairs separately from future reproductions. During the
campaign, existing pinned core classes were borrowed read-only and only these
two overlay classes were compiled. No frozen process was changed.
