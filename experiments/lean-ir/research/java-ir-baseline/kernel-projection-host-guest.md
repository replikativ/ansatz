# Read-only HostGuest result lending

The projection scope may borrow constructor values while an actual completed
HostGuest operation is paused before its result is taken. It neither takes the
helper result nor creates an owner credit.

The runtime exposes this phase only after restoring the helper caller's control
prefix. Admission additionally requires the current engine's exact operation
token and record, matching runtime owner, a complete owned untaken result,
disowned helper arguments, parked outer request, no outstanding Host/Code
request and the exact saved HostCompletion prefix. A claimed completion prefix
is valid; it is not required to be null.

The stamp records HostGuest record/token/outer/parent/result identities, ownership
flags, HostCompletion and completionBase, alongside the existing Program, PC,
request, action, counters and instruction stamp. Taking the result changes the
phase and clears/transfers its record, invalidating cached and uncached access
even if no guest instruction executed. Waiting, failed, advancing, disposed and
closed engines remain outside lending. Close the scope before any guest/helper/
release/take operation; this is not a concurrent or resumable projection API.

Four focused actual-engine tests use synthetic owned constructor layouts. They
cover genuine helper-result borrowing and take invalidation, paused-result fork,
a helper nested under claimed HostCompletion cleanup, and controlled malformed
record flags restored before execution. These are runtime control tests, not
source, ModuleData or kernel association provenance. Run them through
`java-ir-kernel-projection-host-guest-checks/check!` with the accepted basis after
loading the existing HostGuest and projection test dependencies.

Source review is clear. Worker execution is prohibited for this unit, so focused
runtime results and the actual fresh A-to-B retry remain parent-coordinated gates.
The already failed B session must not be resumed or retroactively certified.
