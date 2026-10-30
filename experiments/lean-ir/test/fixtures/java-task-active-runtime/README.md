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
live in a temporary directory and are removed afterward. `LEAN_BINARY` can select a
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
