# Register capture experiments

These are research-only controls over the mutable interpreter, following the
[constructor/cache investigation](INTERPRETER_COST_CORPUS.md). No production
storage, public API, dependency, module inventory or execution default changes.

## Question and two representations

The RBMap size-300 census counted 10,710 join captures and 5,146 jumps with
131-slot registers, plus 16 captures and jumps with 14-slot registers. The
reference interpreter stores an immutable locals map at a join; the mutable
backend normally clones the complete register array. All bound locals, including
dead ones visible in a World, must survive these experiments unchanged.

`join-capture-sharing.clj` shares one cloned array between consecutive stock join
declarations within one run. Jumps still clone before parameter binding. In one
size-300 build/fold, 2,782 captures shared a prior snapshot and 7,944 cloned. The
resident comparison saved about 3% allocation, with little CPU difference. The
cache dies at every public run return; it never keeps guest values in a program.
This probe excludes custom helpers, effectful IDs and concurrent runtime use.

`java/prototype/research/PagedRegisters.java` tests a more structural option:

- Registers use lazy 16-slot pages, retaining the original logical slot IDs.
- A read-only snapshot clones the outer page table and advances the active
  bank's ownership epoch. A later write clones only a nonowned page.
- Repeated snapshots without writes reuse the same immutable capture.
- Forks have independent page tables and initially own no pages. Clearing a
  mutable bank detaches pages; it does not modify saved versions.
- `toArray` exports a copy. The adapter publishes ordinary canonical Worlds.

Physical page ownership is separate from Lean logical RC. No guest retain or
release is added or omitted. This is not a Klara integration or a formal proof.

`paged-registers.clj` adapts register creation, reads/stores, calls, joins/jumps,
delivery, resume and freeze. Frames of width at least 64 use pages; small frames
remain dense. Closure routing materializes dense active locals for the old ABI.
The dense-adapter control uses identical glue with paging disabled, including
its direct-call routing, so adapter overhead is not mistaken for storage cost.

The adapter uses scoped Var replacements on one thread. Custom/effectful IR,
concurrent runtime users, helper redefinition, typed-worker performance and
private host-storage reuse are outside this research contract. All Machines
containing banks must remain inside the adapter scope and freeze before return.
Do not enable this adapter as a general runtime backend.

## Measurements and decision

Native-exported RBMap build/fold, fresh private mutable machine per invocation,
one final freeze. Complete World equality with the persistent reference is
checked outside timing. No hosted frontend, source loading or Init is involved.
Separate 384 MiB JVMs per mode, 40 size-100 and 10 size-300 warmups, seven samples
per size, current-thread CPU and cumulative allocation counters:

| Size 300 | Median CPU | Allocated bytes |
| --- | ---: | ---: |
| Ordinary dense interpreter | 50.737 ms | 45,062,704 |
| Dense adapter control | 50.145 ms | 44,407,824 |
| Final paged adapter | 51.771 ms | 37,538,064 |

The paged adapter saves about 17% allocation against ordinary execution and 15%
against the dense adapter, while taking about 2% and 3% more CPU respectively.
Seven diagnostic samples with different JVM histories do not establish precise
speed ratios. The retained REPL also showed less allocation and a larger CPU
penalty; its raw samples were lost at reboot, so they are not used in the table.

An earlier adapter used `first` to inspect each bank instruction's vector. That
introduced avoidable sequence allocation: its separate-process result was
54.654 ms and 44,510,944 bytes. The final version uses indexed opcode access.
Both versions' separate-process samples survived the reboot and are preserved in
[register-capture-probes.edn](../measurements/register-capture-probes.edn).

The Java/Clojure receipts record 25.0.1/1.12.4. The recovered process identifies
Oracle GraalVM and reports `UseJVMCICompiler=true`; original performance receipts
did not capture that flag. This is not a comparison with HotSpot C2. Allocation
is cumulative thread allocation, not retained heap or required heap capacity.

Keep dense registers as the default. Paging demonstrates a forkable representation
with lower allocation, but does not establish a CPU improvement. Register copies
are only part of the allocation problem. Next prioritize prepared call/jump
execution and typed closed regions; do not infer native throughput from these
storage controls or repeat the earlier sparse-capture CPU regression.

## Ownership and checkpoint checks

The post-reboot 384 MiB REPL reran:

- 500 seeded write/snapshot/fork/clear operations, retaining 120 immutable
  versions and comparing every retained version after every operation.
- Explicit slots 0, 15, 16, 31, 32, 127, 128 and 130, two independent forks,
  writes, clear and read-only rejection.
- Every fuel prefix before a wide-frame suspension/host call; two resumed
  branches with every subsequent fuel prefix, pause/resume completion and
  unchanged parents. Captured joins, caller returns and all visible locals
  match the independent persistent interpreter.
- The same checkpoint scenarios with paging forced on small frames and with
  the dense adapter control.

Independent source review found no ownership/alias blocker within this scope.
The existing unchanged-host storage validator conservatively rejects shared
capture arrays; changing it would require checking every capture context's
body/parameter width, not merely accepting already-seen arrays. No guard was
weakened here. The full compiler/Init/frontend campaign was not rerun.

## Reproduction

From `experiments/lean-ir`, compile the research class into a separate output:

```sh
mkdir -p target/paged-register-research/classes
javac -J-Xmx128m -d target/paged-register-research/classes \
  research/java/prototype/research/PagedRegisters.java
```

Prepend that directory to the experiment's already resolved classpath, supplied
as `ANSATZ_EXPERIMENT_CP` below. Keep production class directories untouched.

```sh
java -Xmx384m -cp "target/paged-register-research/classes:$ANSATZ_EXPERIMENT_CP" \
  clojure.main research/paged-register-clean-probe.clj paged-64
```

Run `ordinary`, `adapter-dense` and `paged-64` in separate processes. For a retained
REPL with the research class directory on its classpath, load
`paged-registers.clj`, then `paged-register-checks.clj`, and invoke
`(paged-register-checks/check!)`. Load the benchmark/feasibility helpers before
`paged-registers/probe`. Load Java once; never reload Machine/Ref classes.
