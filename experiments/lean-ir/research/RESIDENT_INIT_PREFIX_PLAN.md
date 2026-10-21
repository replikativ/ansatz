# Next resident import boundary: checked Init

The [checked Init-prefix preparation/release boundary](RESIDENT_INIT_PREFIX.md)
is implemented and regression-tested. The current
`resident-import/prepare-source-import` still accepts one standalone published
module. The [staged over-Init operation](RESIDENT_INIT_IMPORT.md) is the next
implementation under validation; genuine end-to-end B-over-Init+A acceptance
remains a separate gate. Both preserve checking, executable identity and ownership requirements.

## Preparation and authority

The separate Init-prefix preparation boundary receives the
original successful Init checking result, describes its exact attached native
Source, then calls `source-import/prepare-init-prefix`. It returns a new Context and a
separate issued prefix capability while preserving the input Context. It keeps the original
certificate privately, outside Context metadata that evolves during compilation.

The existing lower-level function treats its checked-result map as trusted host
input. Wrapping an arbitrary caller map in an opaque object does not prove that
the checker issued it. Either mint the capability within a trusted check-to-prefix
operation, or explicitly retain the original-result constructor as a trusted host
boundary. Use an issued-object registry rather than publicly copyable fields.

## Execution profile

Extend readiness checks with the selected native assembly helpers and
`source-import/hybrid-assemble-helper`, alongside header, finalizer and checking
helpers. Authenticate their executable closures and the independently prepared
hybrid binding registry before guest execution. Preserve the exact
`lean_run_mod_init_core` binding identity; prepare hybrid native/local read and
free routing once at the profile boundary.

Keep the first import contract narrow: one published A with the over-Init
profile, no source initializer actions, and actual classic header requests
exactly `[Init, meta Init, A]`. This layout belongs to pinned Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The sibling checkout's later/modified
header implementation must not redefine this runtime's request layout.

Use `assemble-over-init`, genuine finalization, then `finish-over-init`. Every
Init+A constant enters a fresh Java Environment; the source receipt identifies
exactly A. Any projection reuse comes from the privately retained original
certificate, never an optional caller-supplied certificate.

Separate finalizer execution from checking. The existing Init+A experiment
needed approximately 300 million guest steps, exceeding the standalone wrapper's
100M invocation. Reuse cooperative execution with explicit outer, helper and
aggregate budgets. Retain completed IO before checking and the checked packet
before adoption. Failure is terminal; a paused helper does not authorize retry.

## Lifetime and validation

The prefix's world registry owns its guest state; the capability borrows it.
Compatible descendants must preserve registry identity, checked anchor,
immutable scaffold and exact open Source. Releasing a prefix removes only that
branch's registry owner. Context close does not imply prefix release or Source
closure; retained failures, futures and descendants extend lease requirements.

Tests should cover foreign/copy-altered prefixes, stale anchors, closed or
different Sources, native-range shadowing, changed scaffold/bindings/executable
closures, exact header layout, initializer rejection, finalizer errors and
budgets, strict rejection, adoption failure and retained owned evidence. Fork
tests must show that releasing one branch preserves the other and leaves input
Context and borrowed Source unchanged. Finish with genuine ordinary A-to-B
acceptance using fresh checking under the optimized consumer.

This sequence does not add general dependency resolution, change the archived
producer, or infer checking authority from restored state.
