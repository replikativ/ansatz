# Original sequential frontend on the Java interpreter

The pinned authority is Lean `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`
(4.33.1). This gate uses original `Lean.Elab.Frontend.processCommand` IR,
not a replacement parser/elaborator or the earlier Clojure-hosted frontend.
It is separate from complete `Lean.Language.Lean` file/snapshot support.

## Acceptance sequence

1. Construct the real guest environment and original parser/command state.
2. Process `prelude\naxiom HostedSort : Sort 1\n` with `Elab.async=false` and
   `debug.skipKernelTC=false`. Require actual successful checked kernel admission,
   correct ConstantInfo/type, and per-command diagnostics before processing EOF.
3. Extend the corpus to a theorem and executable definition, including rejected
   inputs. Keep logical admission separate from executable IR publication.
4. Add matching imported environments, module IO, and representative project files.
5. Complete queued tasks/pending waits/snapshots and full file diagnostics.

The sequential entry does not import modules, initialize the frontend, or preserve
whole-file diagnostics automatically. Its top-level elaborator resets messages;
end-of-file success or environment membership alone is insufficient evidence.

## Earlier runtime observations — 2026-10-30, before PR #316

The then-integrated synchronous runtime passed 87 suites / 867 test executions /
23,979 assertions in an isolated Java 11 jar with a 384 MiB heap. Its separate
[original-program oracle](../measurements/java-sync-task-oracle-2026-10-30.edn)
validates bounded synchronous dependency behavior, not declaration elaboration.

In a retained 384 MiB REPL, the original sequential frontend's setup completed:
real input context, parsed `prelude` header without imports/errors, genuine
`mkEmptyEnvironment` payload, original `setMainModule`, options, command state,
and state Ref. Only the ordinary four-field Frontend.State record was assembled
by the research adapter from source-verified fields; no frontend body was replaced.

The first `processCommand._boxed` attempt stopped at the unsupported original
`Lean.profileit` extern. The accumulated probe budget at that boundary was
302,957 interpreter work units and 494 additional demanded code bodies (excluding
196 bodies already demanded for the parent environment). No checked declaration
or complete command result was established. These are demand/work counts, not
speed or allocation measurements.

## Value and ownership boundaries

`Lean.mkEmptyEnvironment` returns an IO result: the successful wrapper has tag 0,
one object field and no scalar bytes. The environment payload has tag 0, eight
object fields and one Bool byte. Retain the payload before releasing its wrapper,
or borrow it while the wrapper's owner remains live. A constructor tag alone does
not establish a guest type or Java-kernel association.

The first research attempt mistakenly supplied the wrapper to `setMainModule`;
it failed before declaration processing. The corrected attempt above uses the
payload, and the harness now checks its layout before guest calls. Similarly,
the earlier genuine-environment release experiment released the IO wrapper
containing the environment; it was not a direct environment-root release.

The idle prepared parent is retained. Experiments fork all external roots,
including the owned IO result, so a terminal failed child does not force another
JVM launch or parent reconstruction. Code catalogue storage stays host-scoped.
Failed states preserve diagnostics; arbitrary failed-state unwinding is not claimed.

At the subsequent PR #316 checkpoint on 2026-10-30, with checked-disabled
profiling and UInt64 narrowing enabled, the same original command reached `Lean.Elab.expandMacroImpl?`. Its next stop is the unavailable
initialized global `Lean.Elab.macroAttribute`, after 344,282 accumulated work units
and 652 additional demanded bodies. This advances the runtime gate; it does not
establish axiom elaboration or kernel admission. The profiling option was read
through the original getter using an authenticated captured default, not forced off.

The earlier combined standalone Java gate for those two additions exited 0 at a 384 MiB
heap: 90 suites / 884 test executions / 24,126 assertions. UInt64 narrowing also
matches eight native C-cast vectors through direct and original boxed calls in
both interpreter modes. The integrated Java source SHA-256 is
`97833400f3b286fc7dbb43148367be3c856e86b04418864dda4c3c7a01c81865`.


## Current checkpoint — 2026-10-30, Expr equality integration

The current Java11 isolated jar gate exits0 with **102 suites / 997 test
executions / 52,235 assertions** at a 384 MiB heap. Expr eqv/equal and the two
constructor scalar casts pass 15 focused tests / 679 assertions in each driver.
The runner's 102 expected suite counts were independently matched against the
observed order. Source SHA256 is
`d84d02aa1a38f976de8060c19f21eadfdd8e0a4f8fd038ff4ff4bbed12a048d6`;
tested immutable jar SHA256 is
`948113fd944bb108ed683fffe2d0e7cf8cc26b883d5350bb318019c612317b52`.
The independent 54-case valid-source oracle passes both official Lean `--run`
and generated-C/native execution; that native evidence is separate from the
JVM storage/cycle/resource adversary models.

With the selected companion of 73 globals, the original command now crosses the
cached Expr-data and Expr.eqv boundaries. It reaches 364,725 accumulated
interpreter work units and 1,350 demanded code bodies, stopping in
`Lean.warnIfUsesSorry` at the missing initialized global `Lean.warn.sorry`.
The original frontend has **not** completed this command/file and has not yet
reached the kernel adapter in that path. Expanding the captured companion to 74
is a subsequent experiment, not an established successful declaration.

### Preparation and reusable code observations

Single retained 384 MiB REPL observations show that cold code preparation dominates
these stopped-prefix experiments. They are **not completed-file latency**:

| Earlier stopped prefix | Cold experiment total | Fresh fork/setup with promoted code | New code requests on repeat |
| --- | --- | --- | --- |
| Missing `UInt32.toUInt64` | 9.54 s | 146 ms | 0 |
| Missing `Lean.Expr.data` | 8.06 s | 169 ms | 0 |

In the 9.54 s observation, inclusive code-service time was 7.62 s while guest advance
calls totaled about 75 ms. Nested phase timings overlap and must not be summed as
independent costs. Each warm repeat reached the same unsupported prefix boundary,
with zero newly demanded code bodies; it did not finish elaboration, checking,
EOF or diagnostics. These are individual observations, not a throughput or full
frontend performance claim.

The reusable operation promotes only the actual validated immutable Program
descendant and authenticated Header memo from a failed child into an open idle
parent with the same SourceBinding. Java enforces generation ancestry and
inherited Function, prepared-body and guest-export identity. Published layouts
contain code and immutable literals, not guest Nodes, pending requests or task
records. Parent heap, constant values/readiness, owner counters and policies
remain parent state; the child heap, caches, continuations and failure are not
copied. The observed parent census/counters/policies were unchanged. This is not
a sibling-program merge, initializer replay or general adoption of a child context.
Private host publication remains single-threaded; failed-child disposal/unwinding
is not implied by retaining its code. Further runs fork the warmed parent and
retain the ordinary complete external-owner/remapping precondition.

### Direct native-ABI kernel seam

A separate direct `lean_elab_add_decl` HostRequest probe now validates the narrow
strict empty-base safe-axiom seam. This probe uses a **synthetic data-construction
helper** for the source-verified ConstantVal/AxiomVal/Declaration records; its
Name, Level and Expr values come from original guest constructors. It is not a
declaration produced by the original frontend command.

The actual Java host adapter strictly checked `KernelAdapterProbe : Sort 1`,
executed the original post-check publication helpers, obtained the real
Except.ok reply, and enumerated exactly one original guest ConstantInfo. Its
AxiomVal payload was identical to the still-anchored original declaration, and
the Java checking environment contained exactly that axiom and type. This validates
checking-to-publication correspondence at the native ABI seam; it does not mean
the C++ native kernel ran or that original frontend elaboration completed.
An axiom introduces a named assumption rather than proving a proposition.

The direct probe's receipt also confirms retirement: both association-anchor
credits and caller-owned probe values were released, borrowed source/projection
scopes closed, and the probe guest runtime disposed and closed. These cleanup
facts apply to this probe, not every retained parent/catalogue in the campaign.
The two committed anchor occurrences must be retired before private disposal;
reference equality without guest owner credits is not an association lifetime.

One initial probe error was corrected in the **harness**, not the runtime:
raw root Host entry supplies an owning facade even for a borrowed Declaration
operand. The harness now retains an extra facade credit while preserving its
separate caller Declaration owner. It also records owned readback results before
validation that can throw. Neither correction changes native borrow semantics
or justifies retrying publication after a failed stage.

### Explicit laboratory resource profile

The selected lab heartbeat Host handler returns the interpreter's guest Node
allocation counter. It is explicitly **not native heartbeat accounting**. Actual
original option getters confirm `maxHeartbeats=0`, `maxRecDepth=0`, effective Core
heartbeat limit 0, `Elab.async=false` and `debug.skipKernelTC=false`; the cached
command recursion limit is also 0. Native heartbeat/depth limits are disabled for
this bounded experiment, while host work/deadline, projection and Java checker
fuel limits remain separate. Expr-comparator Java scratch does not fabricate
guest allocations or acquire native heartbeat parity. No default production
resource profile or completed official-frontend/file support is claimed.
