# Explicit Java host boundary, first tranche

Implementation contract, 2026-10-29. This is an opt-in research runtime seam,
not general IO or frontend acceptance. The ordinary builtin registry remains
closed and unchanged. Host descriptors bind original captured symbol, parameter
types/borrow bits and result type; no host callback is executed during prepare,
start or advance. Unsupported/ambiguous descriptors reject explicitly.

The [bounded implementation record](../measurements/java-ir-host-boundary-2026-10-29.edn)
passes 18 host-boundary tests / 131 assertions and the combined isolated jar gate
of 322 executions / 13,231 assertions, using a 384 MiB test JVM. Independent
review found no blocker under the documented thread-confined contract. These
are small captured/synthetic IR programs; no frontend image is restored.

The explicit driver publishes an opaque per-engine request before any host
effect. It records arguments, continuation/destination, boxed-vs-typed return,
root-vs-nested call and surplus application arguments. Host argument accessors
return defensive argument-array copies carrying the same guest identities;
inspection acquires no new guest owner credit. Borrowed arguments remain borrowed;
owned arguments are the handler's explicit consumption/transfer obligations.

Static typed FAP follows those captured borrow conventions directly. Public root
entry and AP/PAP instead receive owned facade arguments. Their adapter keeps the
credits for borrowed target positions while the host borrows them, then releases
only those adapter credits on successful completion. Scalar releases are inert.
Record that disposition per request and copy it through forks. This adaptation
does not consume the handler's owned target positions.

`resumeHost(request, ownedResult)` validates the exact current request and result
lane before changing state. It transfers an owned result once. Returning an
owned argument unchanged transfers that credit; returning a borrowed object
requires an explicit retain first. The engine does not blindly release every
argument: doing so would double-consume valid transfers and discard pending
failure obligations. After reply validation/claim, a failure during adapter-credit
cleanup is terminal and preserves the owned reply and remaining known credits;
cleanup must not be retried. Host handlers can use the engine's existing
retain/release operations. Result validation is not arbitrary graph admission or
a resource capability check.

Invalid, foreign, stale or duplicate replies reject without consuming the
request. `failHost` makes that branch terminal and retains its actual diagnostic
state and cause; it grants no general failed-frame disposal or effect replay.
An invalid reply must not execute a host handler, overwrite completed state or
consume any guest value. While a request is pending, `advance` does not progress
guest execution and synchronous `invoke` must surface suspension rather than
busy-waiting. Recursive execution rejects registered host externs.

Forking a pending request uses the existing single graph-copy memo for its
arguments, aliases, control state and surplus arguments. The child gets its own
request identity and response claim, while exact immutable ABI/code may be
shared. Parent request objects cannot resume a child. Divergent pure replies
demonstrate independent branches; they do not establish authority to duplicate
an external write or resource. Start with deterministic handlers and no real
resources or hidden callback state.

Required gates cover typed/static calls, direct host entry, calls through PAP/
AP, overapplication, nullary host calls, scalar return boxing, nested requests,
per-branch replies, duplicate/foreign/invalid completion, aliased ownership,
terminal failure, close behavior and existing interpreter/fork regressions.
General helper scheduling on the same engine, dynamic linking, kernel carriers
and frontend execution are subsequent work. Do not reenter a running engine or
use the legacy interpreter to hide missing Java execution coverage.

The opt-in research facade is in `java-ir-baseline/repl.clj`: `host-basis`,
`prepare-host-program`, `host-request`, `request-value`, `resume-host!`,
`fail-host!` and `fork!`, alongside `start!`, `advance!`, `take-result!` and
`close!`. A descriptor is a map with `:symbol`, `:parameters` (captured type
strings), `:borrowed` (boolean vector) and `:result` (captured type string).
Preparing a descriptor installs no handler. The caller supplies an independently
authorized handler after observing a request. See `java-ir-baseline/host-checks.clj`
for the bounded call/fork/ownership examples.

The recorded alternating computational control uses the same original RBMap IR
with no host calls. Explicit-driver CPU medians were prior 4.928 ms / host-capable
4.924 ms per execution, with equal allocation near 1.516 MB. Recursive medians
were 3.327 / 3.071 ms. This is a warmed shared-machine control, not an isolated
speedup result or a comparison against native compiled Lean. The repeatable
driver is `java-ir-baseline/host-control.clj`.
