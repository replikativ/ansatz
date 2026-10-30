# Branch-pinned Java executable generations

Implementation contract, 2026-10-29. This tranche extends the typed host-boundary
runtime; it is not itself `evalConst` authorization, module initialization or
frontend acceptance. A caller must authenticate selected IR before preparing it.

The [implementation record](../measurements/java-ir-program-generations-2026-10-29.edn)
passes 15 generation tests / 126 assertions and the combined isolated jar gate
of 337 executions / 13,357 assertions in a 384 MiB JVM. Independent review caught
a recursive-entry gap; both drivers now validate incoming closures before guest
work or ownership transfer. Expanded sibling/private-closure tests pass.

`Program.extend(base, rows)` prepares an immutable descendant. Inherited Function
objects and numeric IDs stay identical; new declarations get appended IDs and
may call inherited functions or mutually recursive peers in the same batch.
Reject duplicate/ambiguous Names, including replacement of an existing binding.
REPL source versions initially extend separate forks of their common base;
in-place redefinition within one generation has no implicit semantics.

Persist defensive immutable copies of typed Name keys. Modifying a caller's
original row/Name lists after preparation must not change future linking. Function
bodies/targets are prepared independently of those mutable input containers.
Host ABI descriptors are inherited; the overload accepting additional descriptors
adds disjoint exact ABIs and rejects duplicate registrations or builtin shadowing.
An extension with no declarations or added descriptors returns the same base.

Each Program has a lightweight immutable generation token. Tokens retain only
ancestor tokens and depth/jump metadata, never a Program, lookup table, function
array, engine or heap. Closures retain their Function and generation token,
not historical complete Program tables. Binary ancestry avoids scanning an
unbounded version chain at every closure call. Current tables may copy references
when extended; structural table storage is a later measured optimization.

An ordinary closure is accepted only when its token is the current token or an
actual ancestor AND its Function object is the exact current function slot.
Sibling generations may reuse an appended numeric ID but remain distinct.
Private runtime closures additionally require the actual current runtime owner;
ancestor code does not convey authority to use another engine's private stream.
All closure entry, application, argument and host-reply checks use the same rule.

`installProgram(descendant)` is allowed only on an open, non-advancing, unfailed
engine at idle or a committed host request. Recursive execution also needs an
empty active stack. Reject paused running frames, pending complete results,
rollback, sibling/unrelated Programs and failed engines. The exact current
Program is a no-op at an otherwise permitted boundary.

Installation preallocates replacement constant/readiness arrays before publishing
anything. Preserve inherited values, identity, RC counts and readiness; new
slots start uninitialized. It executes no code, initializer or callback and
creates no guest owner credits. A pending request keeps its original ABI/call
disposition and once-only identity. The result may subsequently be a closure
from the installed descendant. Forks share immutable code/token state but copy
their constant/control/heap state through the existing graph memo.

`makeClosure(functionId, captures)` creates an owned PAP at idle or a host request,
without reentering guest execution. Validate supported object parameters,
strict underapplication, value carriers and closure generations before taking
capture ownership. Clone the capture array; each occurrence transfers its own
existing owned credit, with no implicit retain. Zero-arity values need later
guest-helper scheduling/evaluation, not an invented closure or replay. Exposed
numeric IDs are scoped to the Program/session that resolved them.

The bounded gates cover immutable input keys, forward links, ancestor closures,
private owner guards, sibling ID collisions, preserved and unready constants,
extension during a pending host call, direct construction of its new callable
reply, independent forked code views, rejected installation boundaries and deep
ancestry without Program/table backreferences. Rooted old Programs intentionally
retain their own tables; this is distinct from accidentally retaining every
historical table through the generation-token chain.

The research facade adds `extend-program`, `install-program!` and
`make-closure!` to `java-ir-baseline/repl.clj`. Preparing a descendant does not
install it; an engine explicitly adopts it at an allowed boundary. The caller
must use the matching Program/session to resolve function IDs.

A paired warmed no-host RBMap control retained equal allocation near 1.516 MB
per execution. Explicit CPU medians were prior 3.333 ms / generation-capable
3.305 ms; recursive medians were 2.901 / 3.070 ms. These shared-machine controls
do not establish a speedup; the recursive difference remains an observation to
watch. No separate local test JVM overlapped the accepted control batches.
