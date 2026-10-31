# Bounded explicit-Prelude projects

`source-module-project-v1` coordinates captured files on one existing source
Exchange runtime. It neither constructs an engine nor manufactures a guest Env.
Use the existing filesystem capture API, genuine header setup, finalizer,
SourceBase and checked driver. The project plan is scheduling data only.

`open-project!` accepts the actual runtime and an ordered vector of
`{:capture capture :dependencies [["A"] ...]}` entries. Captures have the same
text/path/module/SHA/UTF-8 extent contract as the genuine source provider. Limits
are sixteen files, sixty-four direct edges, 64 KiB per file and 512 KiB total.
Every dependency must already occur in the plan. Prelude is implicit scheduling
context and must not appear as a source module or direct source dependency.

For each next file, construct its actual setup and admission bundle using the
existing source APIs. Require setup result `:status :prepared` before opening an
admission driver. Keep that result as `:setup-result` in the bundle; its actual
`:session` must be identical to `:frontend`. For an imported file also include
`:source-import {:finalized-run actualRun :base actualSourceBase}`. This is a
reference to opaque issuers, not a verification flag. The imported scope checks
the exact Base/Run/Closure/selected modules and canonical ready code.

Call `compile-next!` with the project, bundle and explicit companion Headers,
layout directory and command limits. It runs genuine commands, requires every
code batch to prepare/link, retains genuine EOF through module export, retires
the EOF/adapter, and closes source provider/generated scope metadata. It checks
semantic statuses before following effects. Unsupported code, exit, import,
missing EOF or a failed command stops permanently and preserves the actual
active journals. No failure is retried or automatically unwound.

Direct imports are exact. If C says `import A` and `import B`, reconstruct roots
`[A,B]`; closure `[B]` is insufficient even when B transitively imports A. The
original header parser independently checks these requests. A project plan
cannot override parser results or select an unlisted module's ready code.

## Ownership between files

The shared native ModuleLease/original fixed Run/store and each SourceModule's
data/name owners must stay live. After a file's EOF export/retirement, release
that file's frontend setup owners through the same active runtime services.
Its adapter retirement revokes its checking Base. Reopen a fresh strict Prelude
Base from the original ModuleLease/fixed Run for each new source closure; never
reuse a revoked Base. Source closures and their finalized Runs have separate
owner packets and remain guarded until explicit retirement. A live ModuleData
owner, not a raw borrowed Java Node, is the reusable source artifact.

The coordinator retains successful borrowed frontend bundles in `:completed`
and failed preparation/command/export journals in `:active`. `journal` lends
these aliases for diagnostics. `detach-journal!` hands all host metadata back
once and drops coordinator references. It does no guest RC work and does not
declare any failed root disposed. A caller must keep the detached packet until
its actual resources have been discharged or explicitly quarantined.

## Final cleanup recipe

The parent's actual A/B/C run exercised this sequence in a retained 512 MiB JVM:

1. Finish each healthy EOF export and file retirement, close providers/scopes,
   then release known frontend session owners with a fresh idle allowance.
2. Revoke all remaining SourceBases and fresh strict Prelude Bases before
   transferring source finalizer/closure owners. Do not revoke the source
   services needed by callback-capable release.
3. If a legacy session recorded a release at `:not-started` before a deadline
   error, use `take-not-started-release-owner!` with an empty one-slot output
   journal. Release that recovered occurrence once; then release remaining
   session owners. Starting/started/pending records are ineligible.
4. `take-runtime-retirement-owners!` transfers the known source nursery slots
   once. Preserve aliases as distinct occurrence credits. The actual run
   returned thirty source occurrences; this number is evidence, not a constant
   for later projects.
5. Add the original fixed Run/Module retirement packets through their existing
   APIs and perform normal branch disposal while the same providers remain
   active. The actual run released thirty-eight extra occurrences plus 534
   globals, reached disposed-and-closed, closed its store, then closed the
   source runtime. No failure-unwind claim follows from these healthy packets.

This package's new coordinator has pure plan/orchestration models. Parent
operator execution established A/B/C compiler/kernel/result behavior and full
cleanup using the underlying APIs; execution through this coordinator remains
a separate runtime gate. B returned 42 and C returned 43 for input 40. Whether
an imported call survived inlining requires inspecting actual FAP/PAP frontiers;
source references and matching results alone do not establish that detail.
