# Reusable Level session with one context and budget

This stage factors the existing owned Level instantiator into one reusable private
`LevelSession`. It does not implement Expr assignment traversal or enable
`lean_instantiate_expr_mvars`. The [Level algorithm](JAVA_LEVEL_MVARS_RUNTIME.md)
and [private Expr jobs](JAVA_EXPR_MACHINERY.md) remain their existing semantic
implementations, with one shared work-counter abstraction.

`MVarContextCell.current` holds the sole current owned context occurrence. The
standalone wrapper and session never keep parallel context owners. Getters retain
that occurrence into their packets; setters transfer it and leave the cell empty
until a validated return. `InstantiationBudget.work` is the only persisted work
counter, shared by participating Level and Expr workers. The synchronous existing
Level-equality workspace imports/exports that same count in `finally`; it does
not create another allowance. Level cache/saved/frame bounds and Expr frame/cache
reservations remain separate typed resource ledgers, not a globally aggregate
memory cap. Work limits are host profile bounds, not native heartbeats.

A Level job starts from a borrowed caller-anchored Level and performs no input
retain. An empty traversal stack yields one owned result credit. Taking moves
that same occurrence without INC and leaves caches/saved assignments intact for
the next job. Outstanding RESULT rejects restart and seal. Only IDLE may seal;
sealing detaches raw cache keys before their anchors can retire. The caller must
keep those anchors alive through all possible cache lookups, not merely until
one job returns. Saved assignments and cache values stay owned until deferred
session drain. That drain never consumes the shared context cell.

The public standalone Level path preserves pair allocation/context-result
transfer, seal, original input release, saved assignments, cache values, then
successful publication. Context transfer and seal occur in the same VM step, so
no pause exposes a restartable session whose context already belongs to the
output. Source helper policy/ABI/origin checks and smart max/imax/traversal/cache
rules remain unchanged. Level-only callers need no Expr policy.

The fixed private `startMVarSessionResearch` test caller owns two Level anchors,
a context and an Expr input. It runs Level0, one existing Expr lift worker, then
Level1 on the same session/cell/budget. Its private output is an ordinary ctor0
`[context, level0, exprResult, level1]`, not an original Lean ABI or capability.
The Expr worker is a nested existing null-Function action, with ASSIGN completion
into the parent's receiver and next ACTION_BODY. The child/continuation is fully
prepared before publication. Parent is WAIT_EXPR with an empty receiver; after
publication the same ExprCredit moves from parent to child without a tick,
helper, release or extra INC. No root start method is called reentrantly and no
entry/instruction/quota/budget counter resets. Receiver ownership precedes return
validation. The private entry checks source cohort, exact current constructors,
configured Level policy, bounds and known input alias credits before claims.

Fork copies cell, budget, session, batch state, packets and credits through one
identity memo. Parent/child mutable state separates; aliases within each child
remain shared, including the Expr child's budget, the parent budget and the
Level session budget. Raw-key maps rebuild using copied Nodes, and cache/value
indexes preserve credit identity. Only the current action supplies a pending
Level packet; nested unrelated actions cannot claim an ancestor's helper packet.

Existing private test inspection was deliberately adapted to actual session,
cell and budget paths. There are no old scalar counter mirrors or shadow owner
fields retained to satisfy tests. The new focused suite uses existing original
finite fixture rows and clearly labeled setup/helper-body models. It checks
cross-job cache hits, current-context COW/readback, saved-assignment lifetime,
sharing heuristics, nested Code/Host/fork control, result/seal restrictions,
quota/budget continuity, entry rejection and partially drained output escrow.
Failures keep the exact remaining owner/control packet; no successful
failed-engine unwind or general native callback trace parity is claimed.

No JVM test runner, native oracle, image replay, importer change, Node field or
kernel-class change is introduced by this worker. Parent runtime observations
and the combined integration gate are recorded separately below.

## Verified stage-two validation

The parent retained 384 MiB JVM passed the new suite: 11 tests / 148 assertions,
zero failures or errors, on frozen Java source
`b0353d41fe454076b40d574c0b0048f6c6779f1a2c97b1cf58316035a5bd46b5`
and immutable Java 11 jar
`0c9e1d166b4ee3898ce72ef15e8fe871a29f34dd83816ebc1f1d12e3dc179ced`.
Test file:
`fac9d920e720e56a67520392b9c354c0b648733f669920d0979518b76fae0eac`.
Parent receipt `target/java-mvars-session-integration-v1/focused-v3.out` has SHA
`29d3d229eaa69f242c4a58bda15a972416f0031743ac472f694377b61f7c6066`.
The adapted existing Level suite also passed 20 tests / 310 assertions, and the
existing private Expr suite passed 20 / 165 on the same artifact.

One initial test expected quota to decrease at an unprepared constructor's
CodeRequest publication. Source review confirmed the tick belongs to actual
resumed frame entry. The test now checks nonincrease before resume (rejecting a
root-quota reset) and strict decrease after resume. Another focused invocation
failed before execution because a fixture directory remained relative; correcting
the harness path passed without changing the artifact. Neither changed production
quota, ownership or session logic.

Astra independently reviewed the source split, current-context handoff, session
lifetime, nested child publication, fork aliases and final tests. This worker ran
bounded `javac --release 11` with 256 MiB, delimiter/path audits and
`git diff --check`; it launched no JVM/native runner. The parent combined gate is
separate evidence, not an ExprMVars implementation or frontend acceptance claim.

The combined integration on top of the reviewed private Expr machinery, FindExt
and checked Array.set! units passed at 384 MiB: 116 result groups / 1,150 test
executions / 54,259 assertions, zero failures or errors, exit 0. Combined Java
source SHA is `f35e70b4248a461d6f367e73ecd2fb5e4688294e56898e4a13def2dd8d9a4e75`;
immutable jar SHA is
`db5b96548010e51ed7e231606848ab735bb8f76317c5da466fe3a533624dd0d5`.
Parent receipt `target/java-mvars-session-integration-v2/combined-gate-v1.out`
has SHA `95d0edc99fd17be2006b06221ac96d298e6f9b7910c32c312cfaea8eb0a69eb6`.
Integration changed no fixture rows or focused test semantics; the runner retains
all previous groups and adds the eleven-test shared-session group.
