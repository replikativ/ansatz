# Structural Level equality value unit

The Java research interpreter supports the exact `lean_level_eq` borrowed
`[tobject, tobject] → uint8` ABI as intrinsic 409. Together with existing
`lean_level_mk_data` (402), this covers both externs in pinned `Lean/Level.lean`.
`lean_level_eqv` is not registered. The original owned boxed wrapper supplies
first-class/host access and preserves its releases and result boxing.

Implementation enters the existing invocation-local ExprEquality workspace at
EQ_LEVEL. The original Expr entry still starts at EQ_EXPR; traversal, leaf
validation, memoization and existing Expr diagnostics are unchanged. Shared Level
semantics match pinned `kernel/level.cpp:127–158`: kind, low32 hash, pointer
identity, Name IDs, cached regular depth, then ordered children. Cached flags
outside hash/depth are ignored. No Java kernel Level conversion or normalization
occurs. Both Level heads validate before identity shortcuts.

The workspace retains its one-million-work, 100,000-pair and 100,000-stack bounds
and cooperative interrupt checks. Level calls intentionally use the existing
shared `Expr equality ... bounded runtime profile` resource diagnostics. Identity
shortcuts can avoid inspecting deeper malformed/cyclic tails, as in the native
algorithm. Bounds are a host profile, not native heartbeat parity.

All five borrowed Expr equality fences have additive Level guards: public root,
PAP preparation, closure acceptance at AP/admission, prepared import, and host
closure construction. Raw borrowed equality remains direct-FAP-only. Authentic
owned wrapper FAP/AP/import is supported. No Node fields, scalars, RC, metadata,
Program or guest ownership counters are written by comparison.

The [fixture](../test/fixtures/java-level-equality-runtime/README.md) pins the raw
extern and original owned boxed wrapper, source files and shared constructor
rows. Existing Expr-native oracle observations support only the shared
Expr-mediated Level relation; no separate Lean-native direct-Level oracle run is claimed.
The nine-test focused suite runs under default and explicit engines in the
bounded integration gate. The root campaign results below verify the new immutable Java artifact; this
unit does not claim full frontend completion.

## Verified campaign results

Root's retained 384 MiB JVM passed the focused suite in both modes: nine tests /
90 assertions recursively and nine tests / 123 assertions explicitly, with zero
failures or errors. Expected explicit comparator failures preserve their failure
activation/owner packet and reject close until ownership cleanup; the tests assert
that rejection without resetting state or claiming cleanup.

The combined gate exited 0 with 110 result families / 1,075 test executions /
53,250 assertions, including both existing Expr equality modes. It used the same
compiled source SHA256
`7effa38dd94102c178d35c5262eeb748f15b4b4b8b689e363eb510c1ca4f7a50` and immutable Java jar SHA256
`d317f46252c8e315c191f494df3afc8935f2155cb35fe5a58b81b71d34888339`.
The campaign receipt `java-level-equality-integration-v1/combined-gate.out` has
SHA256 `4c65bdcf8de71c0143aab51e48950501f3e8ba7cb560b1e05863a49892ad441f`;
focused results are in that campaign's `focused-v2.out`.

Independent Astra source review confirmed the pinned structural algorithm,
shared EQ_LEVEL entry, all five borrowed fences, exact raw/boxed provenance,
and unchanged existing Expr semantics/error domains. The original Meta solver
then executed Level.beq successfully during the second dependent command and
advanced to the separate `instantiateLevelMVarsImp` native gap before its second
kernel call. This establishes the comparator's integration at that boundary;
general frontend dependent-command completion remains unestablished.
