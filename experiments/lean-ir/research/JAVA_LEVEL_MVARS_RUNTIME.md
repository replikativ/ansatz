# Owned Level metavariable instantiation

The Java research interpreter implements the exact owned
`Lean.instantiateLevelMVarsImp` ABI (`object, tobject → object`) as intrinsic 517.
It returns an owned ordinary pair containing the resulting metavariable context
and Level. This unit does not implement Expr metavariable instantiation or alter
the Java kernel/checker.

An active explicit engine requires a once-installed immutable
`LevelInstantiationPolicy.originalHelpers(getter, setter, succ, max, imax)`.
The five exact ordinary Headers must belong to one source binding, match their
pinned role declarations and remain the current Program Functions. Host/native
substitution and guest-export redirection are rejected. Missing helper bodies
produce normal CodeRequests. Policy is mandatory even when cached `hasMVar` is
false; that fast path calls no helpers. Source byte authentication belongs to the
trusted loader, not to descriptive SHA strings in a Header. Inactive engines
reject before root/AP ownership claims.

The iterative action follows pinned `library/instantiate_mvars.cpp`: preserve
unchanged/unassigned Levels; resolve assignment chains; compress changed
assignments; preserve replaced assignment owners until traversal finishes;
cache only completed shared composite Levels. Sharing uses native exclusivity,
including logical MT, sampled before traversal-induced retains. MVars are never
cached. Smart max/imax simplification runs only after a child changes and uses
structural Level equality plus the native ordered rules. Raw successor/max/imax
construction calls the original helpers to obtain exact cached data words.

The getter receives retained context and Name owners. The setter steals the
current context and receives retained Name/result owners. Helper packets retain
ownership until actual frame or CodeRequest publication; a private entry hook
records that transfer before the entry tick. Receivers own returned values
before result-shape validation. Invalid results and failures preserve their exact
escrow; they are not normal kernel rejection results. Fork copies all control and
owned slots through one identity memo while sharing immutable policy/Functions.

Each owned temporary, input, saved assignment and cache value is released through
the existing resumable release continuation. The output pair stays private until
all drains complete. Deterministic Java traversal/cleanup order does not claim
unsafe C++ binary-expression temporary ordering or universal callback trace
parity. The implementation owns no extra borrowed cache-key/frame-cursor credit.

The profile limits aggregate traversal/equality work to one million units and
frames/cache/saved entries to 100,000, with cooperative interruption checks.
These are explicit host bounds, not native heartbeat accounting. Structural and
assignment cycles encountered during traversal reject. Cached fast paths and
identity shortcuts do not certify every reachable malformed graph or prove
nominal MetavarContext/Level identity from a constructor shape.

The [fixture](../test/fixtures/java-level-mvars-runtime/README.md) contains the
original native/boxed roots and finite helper closure. The active-only focused
suite covers original context/getter/setter behavior, assignment compression,
smart constructors, shared-cache insertion/hits, Code/Host/fork ownership,
resumable Promise cleanup, and terminal failure models. Runtime results are
recorded separately when the parent campaign executes the frozen artifact.

## Campaign validation

The parent retained 384 MiB JVM exercised the unchanged frozen Java source
`16144ba28527689336b71cbfa1763bbc847c551098419114c6d885ba5ab170eb`
from immutable Java 11 jar
`9dc2135591918c2b7aad053de16c95509b456697743b3a5ebdb0cd266adddaec`.
The clean-namespace final focused matrix passed 20 tests / 310 assertions with
zero failures or errors. The parent retained the flat log at
`target/java-level-mvars-integration-v1/focused-final-v2.out`. The combined gate
is recorded separately after completion.

Separately, the parent ran the authentic original parser/elaborator with the
accepted 523-global companion, original Meta guest-export bindings and the five
authenticated helper roles. Two dependent axioms and a three-axiom corpus ending
in `HostedA → HostedA` completed through EOF with strict checking/publication and
successful association/owner retirement. Term-theorem probing reached a separate
missing `lean_array_set` boundary. These are bounded prepared-input frontend
experiments; general file/import execution and self-hosting are not claimed.

The callback test replaces the getter body in a labeled protocol model. It proves
Level control survives a nested claimed HostCompletion's genuine Promise cleanup,
CodeRequest, Host call and fork. It does not claim that a well-typed Level's own
input/saved/cache drain has native finalizers, or that this model authenticates a
producer getter body. Failure cases retain terminal diagnostic/owner packets;
failed-engine disposal or universal finalizer completion is not claimed.

The final combined gate exited 0 at 384 MiB: 111 result families / 1,095 test
executions / 53,560 assertions, with zero failures or errors. The frozen log is
`target/java-level-mvars-v1/combined-gate-v3.out`, SHA-256
`f30ca784ecde9befb1b9efc40b371177ec2cb89df9d57adc80891d7c5e7161e6`.
Two earlier invocations failed before tests because the fresh worktree lacked
`TypedLongMemo` and retained a stale classpath resolved through a class-directory
symlink. Compiling the documented helper into the ordinary ignored classes
directory and forcing classpath refresh corrected the build environment; runtime
source, fixtures and expectations were unchanged.
