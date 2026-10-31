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

Independent source review is clear. The parent ran the four actual HG families
on the accepted F32 basis: 4 tests / 38 assertions passed. The existing projection
suite separately passed 11 tests / 69 assertions. Receipt:
`target/java-source-exchange-v1/projection-hg-models-v1.edn`.
No worker JVM or native execution occurred.

Fresh coordinated A-to-B-to-C execution then passed, including actual imported
declarations, generated code linkage and matching result 43. Root reports normal
retirement of 38 extra owner occurrences and 534 runtime roots in
`target/java-source-exchange-v1/actual-abc-execution-v3.edn`. This does not
certify the separately pending clean-bootstrap artifact assembly. The old failed
B session remains quarantined; it was not resumed or retroactively certified.
