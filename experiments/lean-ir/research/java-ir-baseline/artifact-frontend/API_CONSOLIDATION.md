# Frontend API consolidation slices

This is an implementation sequence over the current research interfaces, not a
public API or a statement that arbitrary projects work. The Java class explicitly
labels itself a bounded runtime profile, and the Clojure basis loads its classes
through an isolated classloader. Existing source, ownership and lifecycle checks
remain prerequisites for each slice.

## 1. Construct the right checked driver

Implemented in this source checkpoint:

- `driver/open-driver` keeps its original sixteen-admission session.
- `driver/open-general-driver` creates `adapter/open-general-session` with an
  explicit ceiling of512, before capturing its runtime dispatch closure.
- `cohort/prepare-general-source-child!` selects that constructor during fresh
  child setup. `prepare-source-child!` remains the finite entry point.

The adapter in the returned bundle and the adapter captured by `:runtime-step!`
are the same object. Replacing one field of an existing bundle is unsupported.
Heartbeat and additional runtime services still pass through the same branch
provider and checked routing wrappers. Parser command, generated-row, runtime
instruction and checker budgets remain separate.

Validation: model the selected constructor, limits and exact session passed to
begin/poll; retain the existing heartbeat, terminal, extra-service and reserved
native-boundary routing models. Then run a fresh generic child in the retained
runtime. Definition loading alone does not validate the guest path.

## 2. Track the general file controller

Add `general-file.clj` beside `general-command.clj`, promoting the reviewed
research orchestration only after its corpus results are recorded. Its proposed
operations are `open-file!`, `next-command!`, `status`, `invoke!` and `retire!`.
The constructor accepts the actual prepared child, source provider and captured
file, not an environment supplied by the caller. Each command creates an M1 Run,
executes the actual parser gate, consumes its CommandReceipt through the M2 scope,
and links or records the explicit unsupported execution frontier before retiring
that Run. EOF is an actual observed eoi command; exit/import are distinct states.

Keep the finite `filesystem-file.clj` and its historical acceptance unchanged.
Tests must include empty input, namespace/section commands with no publication,
multiple declarations/publications, malformed parser recovery, protected-option
rejection, a generated dependency and genuine EOF. A failed Run is quarantined;
the file controller must not automatically resume or unwind it.

## 3. Replace ambient setup with a captured artifact session

Add a research `session.clj` constructor accepting authenticated code/overlay
receipts, prepared module, matched store, runtime policies and source callbacks.
It composes the existing cohort Module/Run/Base/authority factories and publishes
each owner into a journal before the next stage. Move ignored bootstrap glue
into that constructor in bounded pieces, preserving exact pins as inputs rather
than replacing them with a `verified` flag. Return only the operations needed by
slice2 plus an explicit failure owner packet and retirement operation.

Keep `SourceBinding` descriptive: its Java constructor does not authenticate a
catalogue or confer checking authority. Classloader identity, actual source,
current Program and immutable policy identities must be captured once per
session. Test mismatched basis/source, duplicate setup, partial setup failure,
closed catalogue, stale Header, wrong Base/Run, and normal retirement. Do not
claim session fork support until host association and every anchor are remapped.

## 4. Stabilize the Java/Clojure runtime boundary

The current `repl.clj` basis reflects public runtime methods and the research
adapters also inspect private control/layout fields. Do not advertise all public
Java methods or mutable `Node.fields/tag/rc` as a stable frontend API.

First introduce a versioned `RuntimeAccess` in the Clojure layer containing the
already resolved methods used by the new session: start/advance/phase/take,
Host/Code request and reply, HostGuest call/release/result, installProgram,
startRelease/startDispose, counters and policy configuration. Resolve it once
against the actual classloader; reject a missing capability before session setup.
Retain old `repl.clj` functions as wrappers during migration. This is an adapter
extraction, not a change to the VM or ownership rules.

Then add a narrow Java read-only paused-control view for the exact checks that
currently reflect `entry`, caller, bp-relative destination, next Body and
completion state. The view must be stale after progress/close/failure and must
not return transferable guest credits. Migrate one consumer at a time, with
old/new view agreement models and the original parser-gate/HostGuest tests. Do
not replace the current exact-source layout witnesses with nominal type guesses.

## 5. General invocation and imports

Use canonical generated Headers from linked M2 batches for invocation. Add an
explicit typed entry selector and argument schema to slice2; do not retain the
finite Nat-body recognizer as the authority for general code. Keep unsupported
lanes, dynamic AP targets and initializer requirements visible. Validate full
canonical declaration metadata, SCC/static dependency closure and same current
Program/version before calling. Execution success does not issue a new checking
receipt.

Finally add a module graph controller over actual imported artifacts and checked
file versions. Its inputs must distinguish source modules, executable code,
initialized runtime state and trusted imported kernel data. Resolve imports and
module names with exact typed Names and cohort receipts, not filename equality.
Require a module DAG, explicit initialization order/capabilities and actual
per-file source/IR receipts before exposing a project operation. Tests must cover
two dependent source files, import mismatch, unavailable initializer, stale
module reuse and complete owner retirement. Existing matched Prelude trust is
not proof replay, and the runtime companion is not the kernel Init store.
