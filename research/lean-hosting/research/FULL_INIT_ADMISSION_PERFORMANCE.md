# Full Init admission performance: bounded next experiments

Static review, 2026-10-29. This document proposes measurements and design
experiments; it changes no runtime or admission contract. No JVM, restore or Init
run was performed for this review.

## Current evidence

The [genuine full Init artifact/provider record](../measurements/genuine-full-init-artifact-provider-2026-10-29.edn)
passed all seventeen finite stages, including managed disposal, with 65,994 base
declarations and the explicit artifact provenance. Its enclosing admission stage
measured 196.038 s wall, 182.446 s caller CPU and 187,021,061,552 bytes cumulative
caller allocation. Restore measured 91.584 s wall. The nested constructor span
measured 195.766 s wall and 186,773,568,056 allocated bytes; nested spans overlap
and must not be summed. Allocation is not retained heap or whole-process memory.

The earlier [strict run](JAVA_GENUINE_SOURCE_RESULTS.md) reported about 180.7 s
checking and 239.5 GB caller allocation. Different source cohorts and machine
load prevent an isolated comparison. **No startup speedup is established.**

The single SIGQUIT main-thread sample was taken during **prefix preparation**,
not admission. It found `prototype.mutable/freeze-heap`. The prefix stage itself
measured 24.908 s and 32,967,097,152 caller-allocated bytes. That sample identifies
a prefix investigation target; it cannot attribute the admission time or prove
that full heap reconstruction dominated either stage.

The [tiny phase probe](admission-phase-probe.clj) was subsequently run four times
in the retained 384 MiB REPL, using fresh model leases. Its
[records](../measurements/tiny-admission-phase-probe-2026-10-29.edn) confirm one
complete-map projection, one publication snapshot, four issuer inspections/four
projection validations, and two segment validations in every run. Records carry
parent IDs and inclusive/exclusive timings and allocations, with no guest owner
or authority retained. This was an already warmed JVM; neither a cold-start
comparison nor full-Init scaling follows from these tiny measurements.

From `experiments/lean-ir`, load `research/admission-phase-probe.clj` in the small
test-capable REPL and call `(admission-phase-probe/run!)`. It needs the compiled
kernel and `TypedLongMemo` classes plus experiment `src`/`test`, and executes
privately modelled Factory/profile seams. It must not be used to issue or
authenticate a production full-Init projection.

## What admission still does

| Work | Current code path |
| --- | --- |
| Project every selected CI, including types and bodies | [full_init_admission.clj](../src/prototype/full_init_admission.clj), private `projection`; [compact_kernel_projection.clj](../src/prototype/compact_kernel_projection.clj), `make-scoped-projector`; [imported_kernel.clj](../src/prototype/imported_kernel.clj), `project-constant*` |
| Build the complete eager Java Env | `full-init-admission/projection`, repeated `Env.addConstant` |
| Capture complete Java CI shapes and traverse the expression DAG for mutable universe arrays | [kernel_projection_snapshot.clj](../src/prototype/kernel_projection_snapshot.clj), `snapshot-projection` / `expression-array-witnesses` |
| Recheck complete eager Java correspondence | [kernel_artifact.clj](../src/prototype/kernel_artifact.clj), `inspect-for-world`; snapshot `validate-projection` / `validate-eager-domain` |
| Re-enumerate the actual guest map for exact association | [imported_kernel.clj](../src/prototype/imported_kernel.clj), `associate-projection-progress` |
| Check exact attached Store and absence of heap shadows | [module_store.clj](../src/prototype/module_store.clj), `describe-attached`; imported kernel `reusable-projection-sources` |

The compact projector keeps cross-CI Expr/Name/Level sharing and retires scratch
lists/maps after each CI. It still schedules typed vector work items and invokes
the bridge specification/build functions for every required DAG node. Store
cache misses read, hash, parse and validate JSON rows. A compact memo reduces
retention and key overhead; it does not make this an inventory-only admission.

On the successful constructor path, publication captures a full snapshot once.
Association and the final return then call `inspect-for-world` four times: at
association entry, before its helpers, after its helpers, and after association.
Each inspection validates the complete eager domain, CI checking shapes and
captured array witnesses. The two helper-boundary validations additionally call
`validate-segments` over the base segment. These are static call counts, not a
measured time breakdown. Shape checks copy CI metadata arrays into Clojure values;
they do not re-traverse the complete Expr DAG each time. Array validation visits
the previously captured mutable-array witnesses.

Store attachment checks also traverse local heap keys to reject native-range
shadows and rebuild the receiver description. These checks and repeated Name
projection during association are separate candidates from Expr projection.

## First experiment: phase accounting on tiny fixtures

Use the already bounded [full admission boundary model](../test/prototype/full_init_admission_test.clj)
in the retained small REPL. Keep its modelled Factory/profile seams explicit;
never label its privately rebound 17-CI profile as genuine full Init. Run the
existing semantics unchanged and collect scalar records only:

1. Count and measure the complete-CI projector, publication snapshot, each
   inspection and segment validation, guest helper calls, and exact association.
   Record wall, caller CPU, caller allocation, CI count, mutable-array witness
   count and helper target. Give nested spans parent IDs and report exclusive
   totals separately from inclusive timings. Separate first/JIT-cold results
   from a few bounded warm repetitions using fresh model leases.
2. Wrap only admission/projection/guard entrypoints in scoped REPL instrumentation
   that calls each original exactly once and returns its exact result. Keep no
   World, token, CI, source or exception in measurement records. Inspect the
   inner private `projection` through its Var for experiment setup; this does not
   authorize publishing arbitrary projections. Do not wrap mutable storage or
   raw driver functions: identity checks deliberately disable storage reuse when
   those functions are redefined, changing the behavior being measured.
3. Check the expected successful call counts above and preserve existing
   mutation-rejection, helper-failure owner packets, source lifetime and terminal
   one-shot behavior. A tiny result establishes instrumentation correctness and
   fixed/repeated overhead, not full-DAG scaling or a full Init speedup.

If an existing eager Java base remains explicitly host-held after managed
disposal, read-only snapshot/shape microbenchmarks can use its Java objects
without a live Store. This supplies no admission authority. Never invoke guest
helpers or reproject native references after the source lease has closed. If no
such Java base remains, use bounded synthetic Java CI/DAG workloads instead; do
not reopen or restore the full image just to recover it.

The minimal next optimization experiment is **measurement only**, followed by a
separate bounded prototype selected from the observed allocation split. For
example, test allocation-free comparison with original CI shape witnesses while
keeping every existing pre/post check. Do not remove checks merely because their
inputs were recently validated: public CI fields and arrays remain mutable.

## Prefix freeze investigation is separate

[raw_interop.clj](../src/prototype/raw_interop.clj), `run-boundary*`, thaws/runs/
freezes at each mutable/JVM guest boundary. `call` starts a new `drive`; its
optional private machine reuse does not cross independent calls. Default
[module_import.clj](../src/prototype/module_import.clj), `assemble`, invokes one
helper per transported part, one per module, then state/request helpers. Thus
prefix preparation has many boundaries even though it performs no finalization.
The optional `:assembly :bulk` path already exists, but it is not selected by
the current resident prefix API and requires its independently captured helper.

[mutable.clj](../src/prototype/mutable.clj), `freeze-heap`, has three distinct
paths: return an unchanged base; apply only dirty IDs to its persistent base; or
reconstruct the entire local heap when base/dirty tracking is absent or dirty
IDs exceed half the current heap size. A stack frame in `freeze-heap` does not
distinguish them. `thaw-heap` can also scan the whole heap when its storage hint
is missing. [heap_hint.clj](../src/prototype/heap_hint.clj) has a bounded weak hint
cache, so hint misses must be measured, not assumed absent. Full reconstruction
over [HeapOverlay.java](../../../src-java/ansatz/runtime/HeapOverlay.java) also
snapshots keys and creates map entries. Its removal path already removes
net-zero newly allocated IDs from the dirty set; do not attribute historical
temporary allocations to that set without observing it.
The scanned heap is the local guest heap, not the 11-million-node native Store.
`freeze` shares functions/world context, freezes control/registers, and can also
rebuild the globals map when its overlay changed; account for that separately.

On bounded heaps, measure unchanged, small-delta and deliberately large-delta
freeze/thaw cases independently. Use the existing dynamic raw
`*boundary-counts*` for restores/reuses/freezes/reference runs. A later reviewed
instrumentation change could add scalar path/dirty-count/heap-size/hint-hit
counters inside the original storage functions without redefining them. Compare
sequential and existing bulk assembly on the tiny Init transport model only
after authenticating the batch helper. Preserve immutable snapshots, aliases,
RC owners, failure checkpoints and callback boundaries in either case.

## Lazy source-backed artifact Env: possible, but a distinct representation

[Env.java](../../../src-java/ansatz/kernel/Env.java) already supports
`withExternalLookup`, filtered lookup and uncached lookup. Locals override the
external base; ordinary external lookups use a shared soft-reference CI cache.
`sameExternalView` compares lookup/predicate identity. `allConstants` enumerates
**locals only**, and `size` uses `max(localCount, externalSize)`, not base plus
overlay size. Neither method supplies a complete lazy declaration inventory.

A candidate lazy artifact representation would still enumerate the actual
finalizer map once, validate unique typed names/native CI refs, retain the fixed
Store/manifest/profile and token, and validate axiom/unsafe/quotient metadata.
Use an immutable Name-to-native-CI index, then project a complete CI/type/body
only on lookup. `imported-kernel/project-constant-name` already offers bounded
name-only projection. CI envelope/safety metadata can be inspected without
projecting every body. Whether this saves substantial work depends on the number
of CIs/DAG nodes actually forced by the real source workload.

This cannot be substituted into the existing eager projection maps:

- `validate-eager-domain` explicitly rejects external views. Resident prefix
  preparation also expects complete Java CI identity correspondence.
- [checked_delta.clj](../src/prototype/checked_delta.clj),
  `capture-artifact-base*` and `verify-extension*`, enumerate complete Java
  `allConstants`, snapshot the eager base, and use complete name/ref domains.
  They would force the base or reject a lazy Env. A separate artifact-base
  variant must use the authenticated native inventory plus local overlay domain
  and retain the existing strict/eager contracts.
- Original base assumptions and the issued artifact token remain unchanged.
  Strictly checked additions need their own retained guard segments and must
  keep the same actual external-view identity. Description copied into an Env
  extension does not establish that identity.
- Every materialized Java CI still exposes mutable fields/arrays, and its Expr
  DAG can expose mutable universe arrays. Capture original witnesses when a CI
  is first materialized, before publishing it; validate previously materialized
  witnesses around helper/checker boundaries. Do not take a new baseline after
  a callback and thereby accept mutation. Validation must not force cold CIs.
  Related branches sharing a materializer must consult the same stable witness
  owner, including CIs forced later by a sibling. A frozen earlier segment list
  alone would miss them. Checked local-addition segments remain branch-specific.
- A bounded first prototype should keep a strong cache and original witnesses
  for a small forced set, rejecting an explicit force budget. Soft/weak eviction
  is a later problem: guards must not accidentally retain every projected DAG,
  lose witnesses for a still-shared mutable Expr array, or change CI identity
  while live checker caches depend on it.
- The lookup closure must retain only a minimal source-backed projection scope,
  not the entire evolving guest World. The current scoped projector requires
  exact World identity and closes over it, so retaining it indefinitely is not
  automatically a suitable lazy materializer. Keep source ownership external;
  lookup after closure must reject even if an Env cache could otherwise hit.
  The filtered lookup predicate runs before external cache hits and can enforce
  liveness there; local overlay hits bypass it, so operation-boundary lease
  validation remains necessary.

A bounded lazy prototype can test a handful of synthetic source-backed CIs and
one checked overlay declaration: zero cold-body projection at construction,
exactly-once stable forcing, duplicate/base-name rejection, retained provenance,
mutation rejection, and closed-source rejection on cached and uncached lookup.
It must not issue the current full-profile token with a partial `:projected`
map, claim complete eager validation, or silently pass through strict APIs.
Deferring malformed/unsupported expression failures until lookup changes failure
timing and needs an explicit contract decision before production admission.

The next full restore is justified only after bounded instrumentation identifies
which allocation category an implementation targets, its invariants pass, and a
new authenticated source/class cohort is ready. The existing seventeen-stage
acceptance remains correctness evidence for the current eager implementation.
