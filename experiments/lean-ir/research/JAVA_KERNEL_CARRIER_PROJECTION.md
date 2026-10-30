# Borrowed Java carrier checking projection

`prototype.kernel-bridge` now accepts carrier operations without duplicating its
Name/Level/Expr/declaration rules. `make-projector(world, ops)` takes `:ref?`,
`:node` and optional zero-argument `:check!` functions; its original one-argument
form preserves m.World behavior. Safe axiom/definition admission gains an
optional fifth projector argument. The projected Java values are a checking
representation, never replacements for guest values or environments. Name/Expr/Level DAGs are immutable; ConstantInfo
has mutable fields/arrays and its freeze/snapshot/admission policy is separate.

The research [Java adapter](java-ir-baseline/kernel-projection.clj) provides:

```clojure
(let [scope (projection/open-projector basis engine
              {:max-nodes 10000
               :deadline-nanos (+ (System/nanoTime) 1000000000)})]
  (try
    (bridge/admit-axiom (:world scope) kernel-env borrowed-declaration
                       1000000 (:projector scope))
    (finally ((:close! scope)))))
```

`kernel-env` remains the caller's separately associated checker environment.
This adapter does not derive that association from engine or Node identity,
update the guest Environment, publish checked declarations or install IR.
The host protocol must authorize the actual borrowed HostRequest argument or
an explicitly owned helper result. Same-class Java Nodes alone do not establish
engine/source membership; unstamped ordinary Nodes have no general owner field.

The adapter requires the exact isolated engine/Node classes, current thread and
a paused engine. Initial open and every memo hit/traversal check reject closed,
untracked-failed or disposed engines, including states whose phase remains idle. It reuses the current engine's readonly constructor/dead/owner
check and separately rejects closures. Arrays, refs, Tasks, Promises, byte arrays
and other nonconstructor kinds are not interpreted as checking constructors.
The visited allocation must fit the pinned tag/field/scalar storage bounds.
Small views copy only visited Nodes' field vectors and scalar bytes; guest
references remain borrowed. No whole guest graph is copied and no guest RC,
fields, metadata, allocation counters or constants are changed.

Semantic storage checks remain in the original bridge. The adapter maps actual
byte offsets into that existing reader and uses the existing `clone-storage`
validator for complete aligned physical extents. This permits validated native
padding (for example 16 physical bytes for 9 semantic binder bytes), while
unaligned semantic storage stays exact and malformed extents fail. It supplies
no native-source identity or invented object-size witness. Computed caches are
validated as present storage and recomputed by the checker as before.

`max-nodes` bounds distinct visited source allocations, at most 100,000. The
absolute nanoTime deadline is checked throughout the iterative projection,
including semantic memo hits. It is cooperative at projection boundaries, not
a thread interrupter or a replacement for TypeChecker fuel. Neither limit claims
to bound a whole frontend run. Per-invocation view and semantic memos preserve
aliases and reject cycles using the existing explicit traversal.

The scope's world is a fresh opaque token. Its engine, initial operation stamp,
request/PC/Program/action references and thread live only in a mutable holder.
`close!` invalidates that holder, clears the semantic memo under its own lock,
clears borrowed views and drops the engine holder. It is idempotent. Retaining a
closed scope/projector therefore retains no guest Nodes or engine through those
memos/holder. Returned Java kernel values remain ordinary caller values;
immutable Name/Expr/Level DAGs can survive close, while ConstantInfo freezing,
snapshot and admission remain separate obligations. Scalar-only `:stats` reports open/view/projected counts for lifetime tests.
The generic projector exposes documented metadata hooks
`:prototype.kernel-bridge/clear-memo!` and `:prototype.kernel-bridge/memo-size`.

Close **before any guest/helper/release/resume operation**, even if a later
engine stamp coincidentally matches. Stamp checks cover phase, instruction count,
PC, Program, host/code request, runtime action and allocation/RC/store counters;
they detect observed progress, not an unforgeable operation history. The scope
is thread-confined. A failure's existing ExceptionInfo data may contain borrowed
`:value`/`:node` diagnostics; callers must sanitize receipts before retaining them
across later guest effects. Those aliases never acquire owner credits.

Existing semantic limits remain: mdata is erased, letE.nondep is checked then
omitted, raw max/imax can normalize, free/metavariables are rejected, and indices
must fit the checker's supported range. This is not a metadata/fvar/mvar round
trip, common immutable AST storage or a complete kernel port.

The [source-layout fixture](../test/fixtures/java-kernel-projection/README.md)
contains five authenticated original CAS rows, including real axiom constructor
occurrences. Tests import source-layout model descriptors as actual Java Nodes;
they do not claim that the frontend produced those test declarations. In root's
existing 384 MiB retained REPL, the final nine Java Node tests pass 63
assertions and the 13 existing/default-carrier bridge tests pass 114 assertions.
Independent source review also checked the final lifecycle and memo guards. They check a safe
Sort 1 axiom, strict negative types/closedness/safety, unchanged guest ownership,
close/progress/deadline/thread/node caps, cycles/kind rejection and exact/padded
storage. No JVM, full image or native compiler was launched by this agent. Full
repository and genuine frontend integration remain separate root checks.

## Legacy compact projection compatibility

The combined integration gate exposed one existing private consumer: the compact
m.World backend dereferenced private `specification` and assumed its former
three-argument signature. The carrier refactor changed that private signature.
The compact backend now uses the explicit no-doc
`default-world-specification-reader(world)` factory, which returns a two-argument
`[kind value]` semantic decomposition reader. It delegates to the same rules and
does not traverse, memoize or admit anything. The compact walker retains its own
world identity, cycle, lifetime and resource checks; no rules are duplicated.
A source/research/test audit found no other private bridge-helper consumers.

A focused regression proves that the compact walker uses this interface and
keeps baseline results/cache/world checks. Root's retained REPL passes the full
compact suite (13 tests / 22,272 assertions) and the previously failing full-init
admission suite (6 tests / 73 assertions). These bounded tests do not run a full
Init/image restore. A new combined-gate run remains the integration authority.
