# Fixed shim and module-finalizer source setup

Load `java-ir-baseline/source-setup.clj`, then `composite-source-v4.clj` after the
existing Java reflection adapter and catalogue reader. No existing v3 setup or
fresh-bootstrap wrapper changes. This new layer produces source-code evidence,
Headers and setup policy only. It does not run a value action, finalize imports,
issue a bootstrap lineage or admit a kernel base.

`composite-source-v4/authenticate!` accepts the actual open catalogue, captured
source descriptor, and paths `:shim-directory`, `:module-directory`,
`:shim-source`, `:module-source`, `:producer-file`, `:original13`. It authenticates
the fixed shim252-row export and module28-row export, their original source and
producer bytes, pinned receipts/streams, fixed three aliases and thirteen original
source records. The producer binary is streamed with a256 MiB extent bound;
JSON/source inputs have separate smaller bounds. SourceModule/sourceLocal,
row roles, exact typed Names, row counts, base/overlay conflicts and complete local
action lists are checked before a receipt is issued. Complete initializationPlan
metadata remains attached to each ordered overlay; imported initialization plans
are descriptive dependencies of the captured runtime cohort, not replay requests.

The actual effective local action list contains exactly the nonmeta pure value
`JavaModuleImport.finalize._boxed_const_1`, raw rowSHA
`4f9e45cb51441d02006a0a8404f9feb1d13ecffad196cc95d1642d81ed44f66d`.
The source adapter requires that authentic nullary `tobject` row and its runtime
role, dependencies and full source-stream identity. It never supplies a host zero
or records the action as ready. Execute it through the original engine only after
all zero-work policies are configured; preserve its real cache/result ownership.
Startup progress and failure ownership need a separate host record.

Call `source-binding!` once on the opaque issued code receipt. The source-setup
core binds that exact SourceBinding/profile identity and actual catalogue object.
`configure-context` takes receipt, catalogue, current context, SourceBinding and
optional existing Header-by-SHA memo. It validates the complete original Header
ABI/metadata/source before reusing any entry; all overlay Headers are minted once
under that common source. The eight helper Headers, two checked Host ABIs and
three exact guest-export aliases use the same reviewed v3 selection rules.
Header and overlay counts are bounded. Every failure precedes Program registration
or engine execution. The returned local-action Headers identify pending actual
source actions; Header registration does not evaluate them.

Merge `:headers-by-sha` into the real demand driver memo. Its row reader must use
`lookup-entry` for overlays before the accepted base catalogue, preserving original
row digests and direct dependency Header identities. `configuration-callback`
supplies the existing two/three-argument setup shape. `guard-source!` checks the
issued source identity and real catalogue lease. The caller separately guards
current Program ancestry, engine lifecycle, captured runtime state, local startup
completion and any eventual imported-base authority.

Focused metadata models are in `source-setup-checks.clj`: malformed/changed source,
unlisted modules, missing/changed/duplicate actions, shadows, overlapping overlays,
forged receipts, same-SHA altered complete Headers/dependencies, wrong sources and
bad helper ABI all refuse before Program setup. These use source/Header models,
not native producer or kernel-admission claims. Static delimiter and diff checks
passed for this source unit; no JVM, native export or image restoration ran here.

Issued generic evidence is deeply snapshotted into bounded immutable metadata,
including supplied pins, module/action lists, captured-source data and nested setup
rules. Java Map/List mutations cannot rewrite a previously issued profile or its
Header selection. Filesystem File/Path inputs are normalized only for private IO
and are not retained in overlay evidence. Unknown objects, cycles and paths inside
public evidence are rejected without serialization or stringification fallback.
Keys or set members that would coalesce under host persistent-collection equality
are rejected rather than silently changing the supplied evidence.
