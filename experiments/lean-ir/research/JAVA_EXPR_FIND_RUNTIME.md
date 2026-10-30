# Resumable Expr.find runtime profile

The Java engine supports the exact original `lean_find_expr` ABI behind
`Lean.Expr.findImpl?`: two borrowed object arguments, predicate then Expr, and an
owned object result. Support requires the active explicit logical task runtime.
Inactive and recursive entry reject before callback owner acquisition. The
original owned boxed wrapper can be called at roots, by AP, or as a closure;
raw borrowed roots, PAPs and imported closures remain fenced. `findExt?` is not
part of this profile.

The implementation follows pinned Lean 4.33.1 `kernel/for_each_fn.cpp`, including
`for_each_fn<true>`'s partial App visits. Predicate calls occur before children;
App visits function then argument, lambda/forall domain then body, let type then
value then body, and metadata/projection their Expr child. Names, levels and
metadata values are not Expr traversal children. A true callback stops later
callbacks and returns a fresh `Option.some` holding one retained found Expr;
false throughout returns immediate None.

The native likely-unshared hint is tested at each encounter using positive
count one, including a logically MT-marked node with count one. It is not the
engine's mutation-exclusivity predicate. Const/BVar/Sort bypass the identity
visited set. Other persistent or multiply owned nodes use the visited set before
callback INCs. This preserves source ownership-sensitive callback multiplicity;
no extra traversal-root retain changes that hint.

`FindState` belongs to an existing RuntimeAction, not a new guest function or
Node kind. Predicate/root/current, pending entries, visited keys, and the found
cursor are borrowed aliases backed by the suspended caller. Just before each
callback, the engine increments predicate then current Expr and transfers those
two credits to its ordinary AP machinery. Separate flags preserve a successful
first INC if the second fails. Once AP starts, its packet is the ownership
record. The ordinary receiver slot owns a returned object immediately upon
callback return, even before `receiverOwned` is set by the next Find dispatch.
An invalid Bool leaves that object in its receiver escrow; it is not dropped or
silently coerced. Only canonical boxed Bool 0/1 is accepted.

Callback code requests, Host calls, nested searches and release effects use the
existing runtime continuations. Fork copies Find state and both traversal
containers through the same graph memo as the caller/AP/Host state, without
adding owner credits. A found Expr has a separate acquisition escrow until its
credit moves into the new Option field. On successful completion, borrowed
history is cleared. Failure preserves the existing diagnostic packet; there is
no claim that a failed explicit engine can unwind, dispose, close or execute
finalizers. Host references may be retired after diagnostics by their owner.

Expr heads use the existing read-only shape guards. They do not establish
nominal type or validate a whole graph. Callers must supply source-valid,
well-founded Expr storage and a valid predicate ownership graph. Invalid stored
child shapes can fail only when reached. Cycle/forged ownership models are not
newly supported guest values, and no whole-graph RC reconstruction is attempted.

The host profile limits a search to 1,000,000 encounters, 100,000 pending entries
and 100,000 visited identities, with an interrupt check each 1,024 encounters.
These are named rejection boundaries, not native heartbeat accounting. The
callback has the ordinary engine scheduling/budget responsibilities; one search
step does not bound arbitrary callback execution or imply native timing parity.
No Java kernel storage, Expr cache rewrite, nominal tag hint, importer expansion,
or native Meta replacement is introduced.

Evidence is in [the original fixture](../test/fixtures/java-expr-find-runtime/README.md)
and `java-ir-baseline/expr-find-checks.clj`. The focused suite passed 21 tests and 264 assertions in the existing 384 MiB
retained REPL using Java source SHA-256
`3b63c20a602b56ea34cab35a31a52ac223b772c0953e03301fd9acd90e916fca`
and immutable runtime jar SHA-256
`fe8803c7255e7f191743dafc811ad2974731d37dae1e496e8c4a84fbd6cfcd9d`.
No test JVM was launched by the feature agent. The suite covers all twelve Expr
shapes, authentic hasSorry and owned wrappers, dynamic sharing-hint boundaries,
partial Apps, deep chains/shared DAGs, callback Code/Host/nested Find, forks with
visited/pending state, result escrow, failure and limit models. A claimed Host
reply releases its last Promise owner, demands finalizer code, forks, calls Host
on both branches, and finishes without replay while Find remains suspended.
The runner registers Find once in active explicit mode, plus negative legacy
checks within that suite. No complete Init restore, frontend image replay, native
find oracle, or successful default frontend command is claimed by this result.
