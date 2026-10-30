# Runtime initialization phase

The engine models the native boot flag as branch-local runtime state. Default
constructors denote ordinary post-boot execution (`false`). The three-argument
constructor `(Program, explicitDriver, initializing)` can create a fresh
initialization session (`true`). `finishInitialization()` clears the flag only
at an open idle boundary, with no pending result, active stack or failed state.
Completion is one-way and idempotent; there is no ordinary-to-initializing setter.

Original IO.initializing has exact ABI `[void] -> uint8`, not an IO-result
constructor. Its genuine boxed wrapper uses `[tagged] -> tagged`. It reads this
field on each call. Fork copies the flag; finishing a child does not affect its
parent. Header/body/Program/graph operations do not infer or change the phase.
The REPL facade preserves earlier engine jars via optional constructor lookup;
requesting a new initialization session against an older artifact rejects clearly.

Pinned Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` initializes
its native global flag true, then generated main calls mark_end_initialization
before ordinary main. Later imports instead manipulate guest Lean.importingRef;
Lean.initializing is native IO.initializing OR that guest ref. Module completion
guards form a third state domain. Neither a false runtime flag nor the five
imported globals proves that every module initializer has completed. Kernel
Environment construction remains ordinary guest IR, without a fabricated native
kernel object or special mkEmptyEnvironment shortcut.

The prepared-graph API does not authenticate lifecycle claims. Its importer
continues accepting only its explicit graph/cache facts. A source adapter must
bind lifecycle evidence independently to the accepted capture. The current
experimental harness explicitly chooses ordinary execution for the already
accepted checkpoint: its final framed state is done, outside initialization
scope, and has no active initialization/progress/failure tokens. Under the
producer's documented boolean-default rule this means false. This is specific
to that capture; arbitrary graph input does not gain the same authority.

The captured state frame is 695,713 bytes, SHA256
`050d4aa8732944835757330603078d4342eb86964ca0e561f866a6e749dc241c`.
A bounded final-one-MiB read proved equality with the earlier selected frame
inside the previously authenticated checkpoint SHA256
`26282492007e48f6ba06466f0dea2c203c62d918da5ca283aee2db30449e773f`.
No new whole-checkpoint hash, deserialization or heap restore was performed.
This is experimental evidence, not a released authenticated lifecycle loader.

Six tests / 47 assertions run with each driver configuration. Suspension-only
cases explicitly use the continuation driver. They cover original query/wrapper,
fresh/ordinary modes, one-way completion, branch-local forks, graph/Program
noninference, running/unclaimed-result/host/code/closed/failed rejection. Independent
source/fixture/API review is clear. The combined jar gate passes 462 executions /
15,170 assertions across 55 suites at 384 MiB.

The original header probe now reaches twenty loaded bodies and 891 instructions,
entering original EnvExtension.mkInitialExtStates before missing USize.decLt.
This does not establish complete module initialization, parsing, elaboration,
kernel admission or frontend self-hosting.
