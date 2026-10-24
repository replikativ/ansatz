# Managed Project failure disposal

The focused suite passed **109 tests / 2,028 assertions**, including the Project
loader and lower disposal regressions. These optional APIs extend managed
operation abandonment to Project-owned failure branches, without cancellation
or retry. The [validation record](../measurements/project-failure-disposal.json)
records the bounded source-level run.

Terminal construction, load preparation, load advancement/finish and invocation
errors carry an issued opaque `:project-failure-diagnostic` token. Pass it to
`project/dispose-failure!` to retire the library-owned branch. A caller with the
failed load control may instead call `project/dispose-load!`; both aliases share
one private ledger and return the identical idempotent receipt. Prepared, active,
complete and successfully finished controls are not failure-disposal inputs.

The ledger records private Context wrappers and the exact fixed native/graph
child control. It never stores the original Throwable or failure token. Its
reference to the live failed load state is weak, preventing the registry value
from retaining its own weak key through that state's canonical exception.
Successful disposal retires the lower child, abandons owned Context wrappers,
and replaces both library aliases by small disposed tombstones. Successful
returned Project versions and input Projects/Contexts are outside that ledger.

The original caller-held error, its ex-data and any copied snapshots remain
unchanged and can retain diagnostic Worlds. A disposed load subsequently rejects
execution; it does not preserve the old heavy exception in the library merely
to reproduce it after explicit disposal. Keeping a Context wrapper or its public
state Atom also keeps its own diagnostic data. No heap reclamation measurement
or automatic guest cycle collection follows from a scalar disposal receipt.

Disposal serializes on the shared ledger. Child cleanup uses only its fixed lower
API. Context cleanup uses `resident/abandon!`, without guessed RC drops or Atom
callbacks. No Source/Store is closed, initializer or host effect undone, handler
replayed, native external object finalized, or execution retry authorized.
Disposal failure remains terminal and retains pending private cleanup evidence;
subsequent calls reject instead of repeating partial cleanup.

Tests exercise actual Context ownership across reference, mutable and JVM
backends, with compiler/child transport explicitly modeled. Full hosted frontend
IO failure acceptance remains a separate integration gate.

The regression used a 384 MiB heap and 768 MiB process-group RSS cap, took
61.100 seconds and peaked at 650,620,928 bytes for the guarded process group.
All 701 input pins matched after process disposal. No native process or full
hosted frontend was launched for this regression.
