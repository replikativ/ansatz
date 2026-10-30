# Parked host requests and guest helpers

This opt-in control foundation lets an adapter call an authorized original guest
helper, or release an owned guest value, on the same explicit interpreter while
an unclaimed `HostRequest` is parked. It does not implement native kernel checking,
kernel environment association, or checked declaration publication.

`HostGuestPolicy.of(outerHeaders, helperHeaders)` captures exact immutable Header
identities. `configureHostGuestCalls` accepts the policy once at an idle boundary
of an explicitly selected logical synchronous task runtime. The two sets authorize their Cartesian product; there is no per-outer helper
subpolicy. Outer Headers must be actual registered host externs. Helper Headers must be ordinary non-nullary
fdecls with 1–64 owned object parameters and an object result. Use independently
authenticated boxed wrappers for scalar or borrowed native helpers. This first
profile excludes helper entry through initialized constants, nullary fdecls,
intrinsics, externs and partial applications. Transitive guest execution retains
its ordinary supported ABI and request behavior.

The trusted adapter authenticates the Header/source cohort. Neither constructing
a policy nor supplying a `SourceBinding` verifies source bytes, hashes, or an
upstream export association. A source-compiled KernelBridgeShim is a separately
authenticated overlay, not an original Lean declaration.

`startHostGuestCall(outer, helper, arguments)` parks the exact unclaimed request.
Each argument is explicitly `HostGuestArgument.owned(value)` or
`fromHostArgument(outer, index)`. The former requires a caller-owned credit; the
latter moves one owned object argument slot once and records its disposition on
`HostRequest.argumentTransferred(index)`. Borrowed views cannot supply a moved
credit. Original helper code consumes its arguments according to its ABI; the
engine does not release them again after return.

`startHostRelease(outer, argument, count)` uses the ordinary budgeted,
callback-capable release protocol. An outer-slot move supplies exactly one credit;
external owned inputs support nonnegative counts, including zero with normal
carrier validation. External owners must be released before private disposal.
No public synchronous decrement is introduced for active sessions.

Both operations preflight authority, shape and known credit reservations and
allocate their control record before parking or transferring owners. Reservations
include parked owned slots, outstanding operation escrows, claimed host reply
escrows, and each known borrowed facade occurrence. Repeated non-facade FAP
borrowed aliases receive a distinct-node protection floor, not one invented credit
per borrowed occurrence. These checks preserve known credits; they do not prove a
universal owner graph or manufacture ownership for arbitrary Node references.

The operation preserves the actual stack/control prefix, active function/layout,
task scope and claimed host-completion base. It shares the instruction/fuel budget
and current Program, caches and heap. `advance` drives helper code, nested Host or
Code requests, task actions and release work. No recursive host-to-interpreter
entry or alternate interpreter is used. A helper may create a descendant Program;
restoration never reinstalls an older Program or heap snapshot.

Completion enters `host-guest-result`, separate from root `complete`. The adapter
claims the owned result once with `takeHostGuestResult(outer, operation)`, which
atomically restores the original unclaimed outer request. A release result is
Unit (tagged zero). Borrowed diagnostic argument/result views create no credits.
Normal root `takeResult` cannot claim a helper result. A restored outer request
can start another operation or accept its one eventual reply. Original owned
host arguments remain handler obligations except slots explicitly transferred.

Nested helper operations form a parked stack independent of `hostCompletion`.
Failures preserve parked ancestors, argument/result ownership dispositions,
claimed host cleanup state and normal failure diagnostics; they do not restore,
replay, close or silently clean up the failed invocation. Fork copies operation,
request, action, task and heap records through the same iterative memo, retargets
tokens to the child, and preserves aliasing. The existing eager-fork contract
still requires the caller to account for every external owned root; diagnostic
views and duplicate remap roots acquire no credits. Tokens contain no Interpreter
reference. Nesting is bounded to 1024 operations.

A future kernel adapter must close borrowed projection scopes before any guest
helper/release/resume, flatten exception diagnostics containing borrowed guest
aliases, and preserve checked-map identity, quotient flag, source provenance and
anchor lifetime. Node identity alone is insufficient when an environment can
mutate at reference count one. The association ledger must fork with engine
remapping, or reject forks before the first checked publication.

The bounded model suite is `host-guest-checks.clj`. It does not exercise Init,
a full frontend image or an actual kernel association. Full integration requires
separate authenticated helpers, publication checks and association tests.

Validation: the frozen Java source (SHA-256
`f6b1c139795e0753fea1d61c92ae909aa53e7a13a219b857b33c9eefa326cda7`)
compiled for Java 11. The root agent ran the final focused suite in its retained
384 MiB REPL: 12 tests, 152 assertions, all passing. Coverage includes missing
helper code, nested requests, callback-capable release, forks at code suspension
and owned result escrow, parked and already-claimed host completion reservations,
preclaim rejections and terminal frame-entry failure ownership. No new JVM was
launched by this feature worker. Full combined regression testing remains a root
integration gate.
