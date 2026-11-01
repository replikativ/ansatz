# Native active task reference

`Oracle.lean` runs ordinary Lean Promise, BaseIO.chainTask and CancelToken code.
The checked trace establishes deterministic synchronous observations:

- Pending result is unfinished; callbacks registered first/second/third run in
  third/second/first order when the Promise resolves.
- First resolution wins, and dropping an unresolved Promise produces None.
- CancelToken.onSet observes false during set; set returns with true and repeated
  set does not rerun the callback.
- Releasing a two-field constructor containing tokens invokes the second field's
  drop callback before the first field's callback.
- A callback capturing a ref sees the replacement after overwriting that ref
  drops its token. The callback capture is marked MT by the native runtime;
  this tests its exchange-before-DEC branch, not the positive ST branch.

Run `python3 path/to/native-oracle.py` from any directory. Add `--aot` to compile
the original source to C/native code and check the same trace; generated files
live under the ignored experiment `target/` and are removed afterward.
`LEAN_BINARY` can select a
matching installed binary; it must report pinned commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The script checks stdout against the
committed trace and emits a binary/runtime/source/output receipt. The checked
receipt covers both `--run` and C/native execution. It never
rewrites the expected output. The recorded invocation uses Lean `--run`, exits
0 and emits no stderr. No JVM heap is measured by this script.

This is a bounded native reference, not proof of the complete scheduler, native
parallel timing or exact checkpoint-producer executable. JVM active task support
remains planned in [the implementation contract](../../../research/JAVA_LOGICAL_TASK_RUNTIME.md).
The existing Java ready Task.map suite continues to cover the inactive profile.
Although both modes match this fixture, C emission can use known-field release
optimizations absent from original IR. This is not a claim that all source
programs have identical finalizer traces in those modes.

## Pending synchronous ownership cases

`SyncOracle.lean`, `sync-native-output.txt` and `sync-native-receipt.json` add six
separate source-visible cases. Both Lean `--run` and generated C/native execution
match the same checked trace, exit 0 and emit no stderr:

| Case | Observation |
| --- | --- |
| Nested propagation | The last outer registration runs first; resolving an inner Promise drains its callbacks in LIFO order before the outer callback resumes or the next outer callback runs. |
| Duplicate resolve | Dropping the losing CancelToken payload invokes its drop callback before the following effect; the first, already-set token remains the result. |
| Discarded BaseIO.chainTask | Its callback still runs between before/after-resolve effects even though chainTask discards its returned Task. |
| Pure waiting Task drop | The Task is observed pending while held by an IO.Ref. Clearing the holder releases its captured token before the next effect; later source resolution does not retain/rerun that obligation. |
| Deactivation during propagation | A later-registered sync callback runs first and clears the holder of an earlier pure dependent. The captured token drops inside that callback, before propagation completes. |
| Cancellation scope | Canceling the pending source does not make it ready. Its cancellation flag propagates on finish; a sync+ready inline callback inherits the canceled caller scope. After returning to the root the scope is uncanceled. |

The pure map callback only constructs `(token, value)`. Its creation is forced
through an effectful IO.Ref setter, and an effectful `IO.hasFinished` query
confirms pending state before resolution. No effectful observation is hidden in
a pure callback. This avoids relying on pure Task.map placement or unsafe
isExclusive/pointer observations, which compiler floating/CSE and borrowed FFI
temporary owners can invalidate. All callback effects use BaseIO registrations;
there are no sleeps or asynchronous trace assertions.

These observations prove deactivation/capture-release effects, not physical
intrusive-list unlinking. The native runtime may retain deleted task tombstones
until source completion; a logical implementation may unlink eagerly provided
observable order and owner obligations match. The source performs no unsafe
access to a dropped Task. It does not test pending bind forwarding, pending get,
async queues, task priorities, parallel timing or arbitrary finalizer behavior.

Run `python3 path/to/sync-native-oracle.py` from any directory. It verifies both
modes by default; `--run-only` performs the smaller interpreter check. The script
checks the committed source and golden hashes before executing Lean, checks the
exact source commit, compares output bytes, and prints a fresh receipt to stdout.
It **never rewrites** source, golden output or the committed receipt. Generated C,
objects, executable and output captures live under a repository-local temporary
experiment directory and are removed on completion/error. The C link uses one
linker thread; runtime `LEAN_NUM_THREADS=1` still starts the real task manager.

The POSIX harness bounds each subprocess by wall/CPU time, caps files at 512 MiB,
accepts at most 64 KiB per captured stream, disables core dumps, and kills the process group
on timeout. The static native executable observed here is about 120 MB and is
not committed. Address space is not capped: a trial low cap prevented native
runtime thread startup before source execution. This is not a native or JVM
memory benchmark. Source/golden pins are mandatory; recorded binary/runtime,
compiler, archive and generated-artifact hashes describe the successful build,
not authentication of the accepted checkpoint producer or a promise of
bit-identical regenerated executables.

Pinned semantic anchors: `runtime/object.cpp:811–831,892–956,995–1023,1080–1098,
1189–1221,1284–1305,1310–1357`, `runtime/io.cpp:1538–1583`,
`Init/System/IO.lean:244–289`, `Init/System/CancelToken.lean:48–79`, and
`include/lean/lean.h:240–315`, all at the commit above. This fixture is reference
evidence for the planned pending synchronous tranche; it adds no JVM support or
new shipped extern API.
