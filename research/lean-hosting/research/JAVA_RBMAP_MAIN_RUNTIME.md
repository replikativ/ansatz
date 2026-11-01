# Original RBMap main on the Java runtime

The original 80-declaration capture now prepares and executes `main`, including
argument parsing, map construction/fold, decimal formatting and `IO.println`.
This is raw-IR runtime evidence, **not hosted `.lean` loading or public SDK
acceptance**. Source bytes remain pinned in the
[corpus](LEAN_COMPATIBILITY_CORPUS.md); no source rewrite was made. A separate
host harness creates the owning argument list.

## Bounded runtime profile

The additional captured externs implement UTF-8 strings, list-to-array
construction, array size/borrowed lookup, and standard-output retrieval. Strings
remain immutable JVM leaves. UTF-8 positions are byte offsets; supplementary
scalars and embedded NUL are preserved. Fast decode/next validate their proof
domain and reject end/continuation/out-of-range positions. The derived UTF-8
cache uses a weak identity key and retains at most one byte array of at most
1 MiB. String construction has no native capacity-reuse performance promise.

List traversal borrows the spine before consuming its original root once.
Array construction retains each element occurrence before that root release,
preserving shared tails and repeated heap elements. Internal borrowed lookup
does not retain: the original caller's `inc` owns that obligation. Direct host
entry and PAP of borrowed array primitives reject unless an owning guest
wrapper is used; otherwise the current owned-entry contract would be wrong.

Standard output is a six-closure guest `FS.Stream` record. A per-engine root
owns its methods and each getter returns another owner. The boxed closure
arities, including the erased world position, are `[1,2,2,1,2,1]`.

- `flush` and `putStr` return owned IO success/Unit; `putStr` appends verbatim.
- `isTty` returns bare boxed false.
- `read`, `write`, and `getLine` raise named unsupported-operation errors.

Output is captured per engine, not sent to real stdout. Private methods carry
Program and interpreter-owner identities. Foreign methods reject before AP
consumes them. This guard is shallow: a foreign record can enter as an ordinary
constructor, but application of its private field still rejects. There is no
general object-graph admission or cross-engine stream transfer promise.

Ordinary Lean `panicCore` normally diagnoses and returns its retained default.
That policy remains a named unsupported trap here; it is not silently replaced
with an EIO error or a false default. Oversized `Nat.pow` is the separate native
internal-panic case already covered by the Nat profile. The accepted original
main observations use valid nonempty decimal arguments; invalid-input panic
behavior remains outside this profile.

## Iterative release

Long list conversion exposed recursive JVM destruction. Release now uses a
reusable private work stack, preserving one decrement per owning edge and the
existing decrement counters. Duplicate edges, shared tails and persistent RC0
nodes are covered. A short nonfinal-decrement path avoids entering the graph
destructor. The 50,000-cell list test no longer needs Java recursion.

This destructor has no native finalizers or callbacks. It is destructive on
failure, not transactional; underflow, dead inputs or allocation failure can
leave partially discharged owners. It does not provide rollback, general
failed-frame cleanup or permission to decrement every register slot. The list
traversal ceiling is not a guarantee of arbitrary graph size or memory usage.

## Evidence

The [native main oracle](../measurements/java-ir-rbmap-main-oracle.edn) runs the
unchanged source with inputs `0`, `1`, `11`, `100`, `1000`, `10000`, `00011`.
Both Java drivers match its output and IO result shape. The
[string oracle](../measurements/java-ir-string-oracle.edn) covers six strings
and five scalar positions using pinned Lean 4.33.1
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

The isolated jar gate passes 72 test executions / 4,117 assertions in 384 MiB.
New tests cover exact native observations, shared array/list ownership,
private and partially applied methods, independent engines, aliases surviving
engine close, exactly one output append across instruction pauses, named
unsupported paths, and iterative/persistent-node release.

The [runtime receipt](../measurements/java-ir-rbmap-main-2026-10-28.edn) pins
source/artifact hashes, inventories and paired computational controls. Final
RBMap1000/1001 CPU medians were recursive 2.501/2.512 ms and explicit
3.324/3.202 ms (prior scalar/new runtime), with equal allocation near 1.516 MB
per execution. No separate local test JVM overlapped that paired control.
The earlier destructor control and a whole-main diagnostic with a small
concurrent oracle-reader process are retained separately. These observations
do not establish general Lean performance or frontend speed.

Preparation now accepts all original extern declarations, but several runtime
paths above intentionally reject. A zero preparation-error count is not a
complete IO-support claim. Next, connect admitted pure application calls to
the existing source/provider authority as described in the
[heap and closed-region plan](JAVA_PERSISTENT_HEAP_PLAN.md).
