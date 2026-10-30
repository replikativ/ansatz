# Checked-disabled native profiling callback

The research engine recognizes the exact `lean_profileit` tuple
`erased, @object category, @object opts, tobject fn, tobject decl → tobject`.
It requires an active explicit runtime and a separately supplied immutable
`ProfilingPolicy.requireDisabled(actualBoxedGetterHeader)`. Constructors without
that policy reject the native call. Recursive/inactive support, enabled timers,
threshold/reporting/cumulative output and thread-global timing state are outside
this first profile. The independent `trace.profiler` option is not overridden.

The policy accepts only the exact typed private Name
`_private.Lean.Util.Profile.<numeric 0>.Lean.get_profiler._boxed`, original SHA256
`697f802be49ca83e350147ca7a564a73e3162beb454ca78d2990455df96796ed`,
original fdecl kind and owned `object → tagged` ABI. The trusted source adapter
must authenticate row bytes; the policy's supplied digest is not a credential.
At each entry the getter must be the actual registered Header, from the same
SourceBinding as the original profileit extern, without host/export substitution.
The policy holds only that immutable Header, no Program, guest value or reader,
and forks preserve it. The optional six-argument engine constructor and facade
`:profiling-policy` key do not change older constructor contracts.

Every call executes the original getter on one retained Options owner. This
matches `options.to_obj_arg()` in pinned `library/profiling.cpp:12–15` and
`runtime/object_ref.h:44`. The original getter consumes that retained owner and
can demand its own original body/dependencies. In particular, its real
initialized `Lean.profiler` handle must already have an accepted ready value.
It is separate from `Lean.trace.profiler`; absence is a genuine initialized-global
boundary and never permission to use default false. Source pins and two actual
persistent captured handle/Name nodes are in
[the fixture](../test/fixtures/java-profile-runtime/README.md).

An actual false Bool permits the call. True or malformed Bool is a named bounded
rejection before consuming the owned declaration/callback. Options are not
ignored, guessed from a launch flag, or cached by object identity. After false,
the runtime releases the declaration before generic AP of `fn ()`, returning
its exact boxed result unchanged. This matches native `time_task` construction:
its by-value `name` parameter is not captured when profiling is disabled, and
retires at constructor exit, before `apply_1`. When profiling is enabled native
captures the declaration for timer reporting until exit; this implementation
does not claim that enabled behavior.

Source authority is Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:
`Lean/Util/Profile.lean:28–38`, `library/time_task.cpp:57–90`,
`library/profiling.cpp:12–20`, and `runtime/object_ref.h:20–24,44`.
The Lean pure fallback is `fn ()`, but no corresponding fallback fdecl exists in
this accepted catalogue: profileit is an extern and its boxed wrapper is ordinary
IR. The implementation therefore uses an explicitly admitted native control
protocol, not a counterfeit original body or a redirect to guessed fallback code.

The private runtime action tracks getter transfer, declaration release and AP
stages. Guest references remain in ordinary action/stack packets, never hidden
in NodeMetadata. Packet aliases do not create extra owners; the retained Options
copy transfers exactly once to the getter. Fork, CodeRequest, HostRequest and
active finalizer release use existing resumable machinery. Failure remains
terminal with the pending original packet and exact transfer stages retained;
there is no automatic replay or blanket cleanup. Raw borrowed profile roots,
PAPs, public closures and imported closures require the original owning wrapper.
This does not broaden the engine's existing raw borrowed-entry conventions.

The focused suite uses the actual original getter/options code and captured
option handle for default/false/true behavior. Additional synthetic callback
bodies test control transport only: callback code/host pauses, forks, exact float
boxed results, owned-wrapper partial application, missing ready global/policy,
wrong source/header metadata, pre-effect malformed arguments and Bool rejection.
These do not establish frontend completion or kernel admission. No JVM was
launched by this implementation agent; retained-REPL validation is run by root.

Root validation in its existing 384 MiB retained REPL passes 11 focused tests /
73 assertions against Java source SHA256
`1f27ddf07d38c34d2a10e4c8f2ffedef57b0962221f67017493edc7898533ea3`.
The Java 11 draft compiled successfully. Root's genuine sequential setup and
first processCommand probe with the authentic 45-global companion and this
policy passed the profileit boundary, then stopped at unavailable UInt64.toUInt32
in Command.withInitQuotContext (343,278 cumulative instructions / 616 new
bodies). This is parent-run integration evidence, not declaration success or
checked kernel admission. The combined full gate remains an integration check.
