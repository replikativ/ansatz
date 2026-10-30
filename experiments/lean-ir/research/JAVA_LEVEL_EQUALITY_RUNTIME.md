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
Expr-mediated Level relation; no new direct-root native execution is claimed.
The nine-test focused suite runs under default and explicit engines in the
bounded integration gate. Verification remains pending the root's new immutable
Java artifact; this source change does not claim full frontend completion.
