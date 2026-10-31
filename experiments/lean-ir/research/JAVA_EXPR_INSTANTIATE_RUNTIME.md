# Original pure Expr instantiation and lifting

The active explicit runtime implements six original borrowed natives at IDs
524–529: `Lean.Expr.instantiate`, `instantiate1`, `instantiateRange`,
`instantiateRev`, `instantiateRevRange`, and `liftLooseBVars`. Configure the
existing immutable `ExprTransformPolicy` while idle. Every entry validates its
source cohort and all nine current ordinary constructor helpers, including
identity paths. This enables no full expression-metavariable native.

All raw arguments are borrowed; the unchanged original boxed wrappers release
their owned arguments after receiving the result. Direct FAP and owned wrapper
root/AP calls are supported. Raw root, PAP, makeClosure, imported closure and
returned raw closure fences remain. The trusted loader authenticates original
code; descriptive Header hashes alone do not establish source authority.

The visitor follows pinned Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, `kernel/instantiate.cpp` and
`replace_fn.cpp`. Forward substitution reads the selected live Array slice in
ascending order, reverse substitution in descending order. Slice indices are
not loose-variable cutoffs. A substituted expression is lifted by the current
binder offset; remaining loose indices decrease by the slice length.
`instantiate1` borrows its single expression without creating a guest Array.
App function precedes argument, domains precede binder bodies, and let type/value
precede body. Rebuilding uses original constructors and preserves other payloads.

Forward empty substitution returns the original identity. Reverse empty visits
loose variables, rebuilding affected leaves and ancestors; closed expressions
still return identity. This distinction applies only to the public slice view:
private substitution and beta jobs keep their earlier empty fast paths.

Range parameters are canonical nonnegative mathematical Nats represented by Long
or exact immutable BigInteger. Small BigInteger host models follow the same
mathematical domain as Long; this does not reconstruct a noncanonical native
small-MPZ tag. Invalid slices, including heap-sized endpoints, reject before
native claims even on closed input. Native panic execution is unsupported.
Lift parameters above signed63 return identity. Smaller parameters narrow to
unsigned32 before use; the delta retains its full unsigned32 range. Cutoff and
zero-delta shortcuts follow that narrowing. Rebuilt indices use exact arithmetic;
results outside the source 20-bit cached loose-variable range reject instead of
truncating or silently clamping.

A borrowed immutable slice retains backing aliases without acquiring guest
credits. Native actions retain input/Array through the parked caller. Offset
jobs cache by `(Expr identity, binder offset)` with the native `rc != 1` heuristic,
which ignores logical MT at RC1. This remains distinct from arbitrary callback
replacement's nonexclusive identity cache. Cache entries, constructor arguments,
returned receivers and retiring credits reuse the typed ownership ledgers.
Same-memo fork copies the borrowed slice, frames, constructor/control packets,
cache and output credits. Failed actions retain unfinished state; no general
failed-session unwinding or callback completion is implied.

Limits reuse the one-million aggregate work budget, 100,000 frames/cache entries,
and cached loose range at most 1,048,575. Structural cycles encountered during
traversal reject. Valid source cached words and acyclic Expr storage are required;
forged constructor/control failures are explicitly backend models. A separate
nested native invocation has its own visitor budget while sharing engine fuel,
Program and continuations. No native heartbeat, exact allocation/RC trace or
unbounded overflow behavior is claimed.

The [fixture](../test/fixtures/java-expr-instantiate-runtime/README.md) pins twelve
raw/boxed rows and a complete 63-row static helper closure with no initialized
globals. This adds no image root and does not establish closure of unknown dynamic
or native calls. Its erratum distinguishes queue exhaustion from complete
resolution in earlier metadata reports.

The parent retained JVM passed the frozen fourteen value/control tests with
210 assertions on Java source SHA-256
`42ff960c1caf16477aa2ffd83de95f90529de7b41539db32d660388d81007aca`,
jar SHA-256
`d7bae566ffd9671c1890b1cf57db9b680a6f64c88f10311c28a0eae9956c085f`.
The separate five-test policy/failure supplement passed 36 assertions on the same
source and jar. It covers unconfigured/inactive identity entry, all raw PAP
fences, constructor Host suspension with divergent fork/failure, live-cache
fork drains and aggregate-work failure. Its first run exposed a test-only String
instead of Throwable argument to failHost; correction required no Java change.
The pinned native `--run` oracle matched nineteen expected content/identity
observations, exit 0 and empty stderr; its receipt explicitly claims no AOT or
JVM equivalence. Full combined integration and original frontend completion are
separate gates. Individual limits and interruption points are not exhaustively
tested.
