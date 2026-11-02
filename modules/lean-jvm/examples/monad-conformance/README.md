# Init-only monad conformance

The candidate corpus has passed 22 official-native/JVM comparisons, nine retained
handle checks and the prepared-artifact path. The packaged Java/Clojure consumer
also checks uncaught IO errors and branch cleanup. Reproduce the gates below;
these observations are not a claim of unrestricted monad/runtime coverage.
Use the official Lean 4.33.1 cohort at commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, matching the producer bundle.
`Main.lean` imports only `Init`; the independent `NativeOracle.lean` imports the
fixture module and prints deterministic tab-separated IDs and EDN values.
Neither a Lake project nor an added dependency is required.

Only closed monomorphic functions cross the public boundary. Transformers,
references, error handlers, and finally callbacks stay inside Lean. Host results
use the existing Nat, Bool, String, Prod, List, Except, and Option carriers.

| Entry | Host arguments | Effect | Expected values for the helper's cases |
| --- | --- | --- | --- |
| `readerStateExcept` | Nat, Nat, Bool | pure | `(3,10,false)` → `[{:ok 13} 13]`; true → `[{:error "body"} 13]` |
| `stateRollback` | Nat | pure | `10` → `{:ok [11 11]}` |
| `stRefs` | Nat | pure | `10` → `[10 [15 true]]` (old value, final value, alias identity) |
| `estFinally` | Bool, Bool | pure | false/false → `{:ok [7 {:some 7}]}`; true/false → `{:error "body"}`; either case with cleanup true → `{:error "cleanup"}` |
| `exceptTFinally` | Bool, Bool | pure | Same four outcomes as `estFinally` |
| `baseIORunner` | Nat | IO | `10` → `[10 15]` |
| `eioRunner` | Bool | IO | false → `{:ok 23}`; true → `{:error "typed"}` |
| `stateRefRunner` | Nat, Nat | IO | `(3,10)` → `{:ok [123 123]}` |
| `stateRefDiscard` | Nat | IO | `10` → `15` |
| `ioCatchFinally` | Nat | IO | `10` → `[21 121 1121]` |
| `retainedRead` | none | IO | Fresh Project → `40`; after the two bumps → `45` |
| `retainedBump` | Nat | IO | Retained calls with `2`, then `3` → `42`, then `45` |
| `uncaughtUserError` | String | IO | Throws GuestIOError with immutable bounded userError details |
| `legacyUserError` | none | IO | Throws a fixed userError; source checks exercise legacy IO Unit selection separately |
| `otherIOError` | none | IO | Throws GuestIOError with empty details; its constructor is outside the partial public projection |

There are 22 ordered oracle cases. All IO adapters emit empty stdout/stderr.
The helper also calls the same retained `stRefs`, `baseIORunner`, and
`retainedRead` handles three more times (nine checks). Fresh local cells must
start with their argument, while the initialized global must remain at 45.
Run `check-project!` once per newly loaded Project; it deliberately does not
reset the global between runs or hide startup failures.

## Source authority

All upstream anchors below refer to the
[pinned Lean tree](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6):

- `src/Init/Control/Reader.lean`: ReaderT passes its unchanged environment to
  the underlying computation.
- `src/Init/Control/State.lean:32–57,95–100,160–165`: run/bind thread state;
  StateT's catch invokes the handler with the state at entry to the caught
  action. Consequently the +100 in `stateRollback` is rolled back.
- `src/Init/Control/Except.lean:141–165,323–331`: ExceptT.run exposes the
  underlying result. State underneath ExceptT survives its typed error;
  ExceptT.finally gives the cleanup error precedence when both actions fail.
- `src/Init/System/ST.lean:94–117,145–159,186–197,238–290`: EST.catch threads
  the post-error world; EST.finally runs cleanup for either outcome and lets
  its error win. runST/runEST allocate the erased world; ref wrappers provide
  get/set/swap/ptrEq and modify. `modify` uses the upstream take/refill
  implementation replacement, without exposing unsafe functions to the host.
- `src/Init/Control/StateRef.lean:23–48,101–110`: StateRefT.run allocates and
  reads back a real reference; run' discards its final state. Catch passes the
  same mutable cell to its handler, so mutation survives the caught error.
- `src/Init/System/IO.lean:39–140,149–175,1662–1673`: BaseIO/EIO aliases and
  BaseIO.toIO / EIO.toIO' adapters preserve values and typed errors; IO.Ref
  uses the ST reference substrate.

Named regular global initialization and repeated calls have been exercised
through both source and prepared-artifact loading. This uses the current named
regular-entry startup path, not builtin or anonymous initialization, and exposes
no guest reference cell to host callers.

## Retained REPL use

From `modules/lean-jvm`, load the helper in a fresh namespace of the existing
packaged-SDK REPL. It starts no processes and opens no projects on load.

```clojure
(binding [*ns* (create-ns 'monad-campaign)]
  (clojure.core/refer 'clojure.core)
  (load-file "test/monad_acceptance.clj"))
(in-ns 'monad-campaign)

;; Reuse an existing runtime, or explicitly create and later close one.
(def runtime (lean/open))
(def compiler {:sysroot sysroot :producer-bundle bundle :cache cache})
(def project (open-project! runtime compiler "examples/monad-conformance"))
(def source-result (check-project! project))

;; Separate, explicit official-native stage. Use a new receipt directory.
(def native-rows
  (native! sysroot "examples/monad-conformance" "target/monad-native-001"))
(compare-native! source-result native-rows)

(lean/close! project)
(lean/close! runtime)
```

`native!` first creates `Main.olean` using the supplied official executable,
then runs `NativeOracle.lean` using that executable's `--run` path, with
`LEAN_PATH` set to the receipt directory. Compilation and oracle execution
have separate stdout, stderr, command, and exit receipts. This provides
official-executable differential evidence when run; it does not claim a C
backend executable comparison. It does not alter the source directory or
the user's Lean source checkout. Source-load success alone never marks a
native comparison successful.

## Gates and limits

Expected runtime externs are the already registered/admitted ref family
(`lean_st_mk_ref`, get/set/swap/take/ptr_eq), `lean_void_mk`, and startup
initialization/persistence support as demanded by actual generated IR.
No filesystem, tasks, clocks, process, network, generic FFI, guest Ref codec,
or higher-order public arguments are needed. No new primitive is proposed.

Preparation, closed-entry proof, ownership/provenance admission, named global
startup capture, and execution are still separate gates. Actual exported
IR/extern closure has not been collected here; an unexpected extern or
projection refusal must remain a visible blocker. The oracle alone uses
official stdout, string rendering, and local module loading; those are not
added to the JVM fixture's public entry set.

This checks guest error/finally semantics on ordinary returns. It makes no
cleanup guarantee for host resource limits, cancellation, panic, abandoned
Projects, empty-cell waiting, concurrent ref access, or external resources.
It does not test public uncaught IO.Error detail transport, prepared-artifact
reload, Std/Lean imports, or frontend monad applications. Add those as
independent increments after this candidate has real receipts.
