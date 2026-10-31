# Bounded interpreted initializer publication

This internal protocol implements one regular `[init]` declaration/initializer
pair. It does not establish complete Init startup, kernel hydration, eager
ordinary-nullary C startup, module loading, native execution, or entropy support.
Its tests are interpreter protocol models, not native evidence.

Pinned reference: Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:

- `src/Lean/Compiler/InitAttr.lean:159-203`: native fallback, module entered before
  actions, deduplicate private/IR attribute entries, execute in module order.
- `src/library/ir_interpreter.cpp:1127-1146`: invoke named initializer, on IO.ok
  mark the actual payload persistent, decrement the wrapper, publish that same
  payload as the target global; on IO.error return the original owned result.
- `src/include/lean/lean.h:3034-3061`: IO result is plain tag 0/1, one object
  field, no scalar bytes. Success status is a newly owned IO.ok boxed Unit.

## Engine methods

`void startInitializer(Header global, Header action)` requires explicit
initialization, no TaskRuntime, one SourceBinding, original registered Headers,
an initialized boxed nullary fdecl returning `object` or `tobject`, and an ordinary
`(void) -> object` action. The actual `IO.stdGenRef` global uses `tobject`;
the action result ABI remains `object` independently of that global ABI. Scalar
globals and the broader `tagged` header type are not admitted by this protocol.
The action's exact typed Name must match `global.runtime.initializer`. It does
not accept any caller-provided payload. Header/source metadata remains trusted
adapter input, as in the existing Header API; this is not source authentication.

The method preflights invocation then records an attempt before starting the
execution. Attempts cannot replay. Guest execution uses existing `advance`,
code-demand and host-request protocols; source-backed descendant programs can
still be installed to satisfy demands. Ordinary start/result extraction, fork,
and finishInitialization cannot bypass a pending initializer.

`Object completeInitializer()` requires the actual completed owned result from
that invocation. IO.error transfers the same wrapper, claims no payload credit,
leaves the global unavailable and forbids finishing startup. The caller must
release the returned owned result. IO.ok returns an owned IO.ok Unit status.

Success preflights wrapper/global identity, shape, live payload, bounded
persistent traversal, release scratch and cancellation. It allocates the status
before any persistence mutation. The commit only sets persistent RCs, consumes
one wrapper credit and publishes the payload into the existing constants slot.
There is no generic release callback in this commit: a known plain one-field
wrapper has only the now-persistent payload as its child. A shared wrapper loses
one credit and retains its field; an exclusive wrapper is made dead and cleared;
an already-persistent wrapper remains intact. No INC is needed for persistent
payload publication. Scalar/immediate payloads obey the existing unlimited-credit
rule. A rejected completion leaves the result engine-owned and the cache/RCs
unchanged. Closing a completed rejected invocation uses existing owned-result
cleanup. Guest execution failure retains diagnostic frames under existing
terminal engine semantics; this change adds no rollback or discard operation.

## Outer module ledger (separate work)

A reusable project adapter must read the accepted module ordering and exact
regularInitAttr entries from saved source metadata; concatenate private and IR
entries with structural pair deduplication. Mark a module ENTERED before its
first action, including an empty module. Track RUNNING/SUCCEEDED/FAILED/CANCELLED
as diagnostics; ENTERED is the at-most-once authority, so failures/cancellation
must not turn the module back into an unentered module. Resume a suspended
execution only through the existing explicit protocol. Do not restart an action
whose side effects may already have happened. Only call finishInitialization
after all selected actions succeed. Fresh-engine restart is an explicit separate
operation, not a retry on a mutated engine.

The inspected savedV3 metadata has two identical private/IR regular-init entries
for `IO.stdGenRef`; deduplication yields one action. This bounded engine feature
neither loads that action nor claims it ran. Anonymous/builtin handling and phase
selection remain outside this initial feature.

## Random extern ABI (separate work)

Pinned `src/Init/System/IO.lean:428` declares
`getRandomBytes (nBytes : USize) : IO ByteArray`. Pinned `src/runtime/io.cpp:863`
implements `lean_io_get_random_bytes(size_t) -> obj_res`; the C ABI erases World.
The boxed wrapper in pinned `stage0/stdlib/Init/System/IO.c:6716-6724` has boxed
USize plus erased World and calls the one-argument C function. An interpreter
HostExtern must match the original exported IR Header, expected to be
`[usize, void] -> object`, borrowed `[false, false]`, rather than copying the C
parameter count. The actual captured extern row must be checked before admission.
This commit registers no entropy extern and supplies no random bytes.

## Validation

`initializer-publication-checks.clj` exercises identity/RC ownership, shared
wrapper handling, exact pair binding and ABI rejection, incomplete/stale
completion, post-boot refusal, error ownership and at-most-once behavior,
interrupted/invalid completion atomicity, and terminal guest failure.
The root compiled the single Interpreter source once using `javac 25` with
`--release 17` and a 384 MiB compiler heap. The compiler emitted the existing
strictfp warning. The root loaded the new classes in the existing retained
512 MiB REPL through a new class basis; the old engine jar remained unchanged.
No worker JVM or native process was launched for this feature.

The corrected initializer models passed 9 tests / 72 assertions. Existing
initialization, fork, header, generation and release-transaction suites passed
58 tests / 7,192 assertions against the same new class basis. Combined result:
67 tests / 7,264 assertions, zero failures and zero errors. Initial model tests
had four errors because a nullary constructor payload is an immediate Long;
test-only commit `06144050` corrected the heap payload and added an explicit
immediate-payload case. Java source did not change between those runs.

The independent source review cleared `06144050` against the pinned upstream
initializer semantics. Additional persistent-wrapper, payload-to-wrapper cycle,
and code-demand/fork scenarios are useful future tests; they were not executed
by this validation. No native initializer, random extern, actual Init startup,
or kernel execution is established by these model results. Portable source pins,
external log digests and exact suite counts are in
[initializer-publication-validation.json](initializer-publication-validation.json).

## Commands used for validation

Run the compiler command from the Ansatz repository root. Paths below are
repository-relative equivalents of the root's worktree paths; no build command
was run in the landing checkout.

```sh
javac -J-Xmx384m --release 17 -d target/initializer-publication-v1/classes experiments/lean-ir/research/java-ir-baseline/src/ansatz/research/ir/Interpreter.java
```

In the existing REPL with the repository's usual check namespaces/dependencies
already loaded, the root used a new class basis and loaded the corrected model
file. Here `j` is the existing alias for `java-ir-baseline`.

```clojure
(def initializer-publication-basis-v1
  (j/class-basis "target/initializer-publication-v1/classes"))
(load-file "experiments/lean-ir/research/java-ir-baseline/initializer-publication-checks.clj")
(with-open [writer (clojure.java.io/writer "target/initializer-publication-v1/models-v2.log")]
  (binding [clojure.test/*test-out* writer]
    (java-ir-initializer-publication-checks/check! initializer-publication-basis-v1)))
```

The root then invoked these existing checks with the same class basis, binding
`clojure.test/*test-out*` to `regressions-v1.log` for the first four suites and
`release-v1.log` for the release suite. Existing check dependencies were loaded
from the primary checkout, including byte-array/pointer/release dependencies.

```clojure
(java-ir-initialization-checks/check! initializer-publication-basis-v1)
(java-ir-fork-checks/check! initializer-publication-basis-v1)
(java-ir-header-checks/check! initializer-publication-basis-v1)
(java-ir-generation-checks/check! initializer-publication-basis-v1)
(java-ir-release-transaction-checks/check! initializer-publication-basis-v1)
```
