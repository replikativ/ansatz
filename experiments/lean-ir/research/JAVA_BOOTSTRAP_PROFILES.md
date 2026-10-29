# Provider startup profiles

Source-grounded Astra review, 2026-10-28. The proposed fast profile is not
implemented. Current genuine acceptance continues to use fresh Java checking.

This distinction applies to the experimental hosted frontend. Normal Ansatz
already loads bundled Init in TRUST mode: `core/init!` calls
`bundled-medium-env false`, and `core/load-init!` defaults to `:verify? false`.
Prepared stores use `export.storage/load-env` without replaying every declaration.
The expensive strict replay measured below is not normal Ansatz startup.

## Distinguish import policy from source hosting

Pinned Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
`src/Lean/Environment.lean:2307–2389`, installs imported ConstantInfo maps into
Kernel.Environment in `finalizeImport`. It does not replay declaration checking;
it explicitly assumes nonempty imports initialize quotients. New declarations
use checking in `src/kernel/environment.cpp:287–294`, with checking enabled by
default in `environment.h:97`.

Freshly checking the complete imported base is therefore stronger assurance
than normal native Lean import. It is valuable for validating this JVM kernel
port; it need not remain the prerequisite for every provider restart. Ansatz's
existing prepared-store documentation (`doc/stores.md`) already distinguishes
loading stored declarations from checking every proof at startup. Serialized
`:verified true` is not checking authority.

| Profile | Imported-base authority | Startup work |
| --- | --- | --- |
| strictFresh, current | Actual Java replay under recorded policy | Restore and check the complete base |
| trustedArtifact, proposed | Explicit provider admission of a pinned distribution/cohort | Authenticate selected identity, reconstruct matching representations and establish their association |
| checked checkpoint, later | Trusted producer's earlier check, bound to checker/artifacts/policy | Verify provenance and reconstruct exact semantic state; not a fresh check |

Signatures identify an issuer; reproducibility supplies production evidence;
hashes establish identity relative to a trusted expected digest. None alone
proves logical validity. A manifest's self-assertion cannot select its own trust.

## Positive construction

1. Provider-controlled admission selects an exact supported Init cohort: kernel
   data, guest ModuleData, frontend/runtime IR, actual Java classes, helper/binding
   registries and preparation policy. Kernel stores alone lack frontend companions;
   older bundled resources must not be assumed compatible with the 4.33.1 profile.
2. Construct the immutable Java environment with exact ConstantInfo meaning:
   universe parameters, types, definition bodies, safety, reducibility hints,
   inductive/constructor/recursor metadata and quotient state.
3. Establish that the guest map represents precisely the same admitted base,
   either by actual comparison or by construction from the same immutable source.
   Retain root/map/source ownership and prohibit shadowed source identities.
4. Check every new declaration through the existing kernel admission operation,
   including generated inductive families; extend the association after successful
   checking and publication. Preserve explicit axioms as assumptions.
5. Retain source-unit, executable closure, initialization, generation and lifecycle
   checks. A valid kernel declaration alone does not associate arbitrary runtime
   code with that source.

The conditional invariant is: given admitted base Γ and its faithful
representation, each new accepted declaration is checked against Γ and the
association extends to Γ plus that declaration. The checker consumes lookup,
universe and safety facts; it does not require the history of how Γ was admitted.
This does not independently validate a malicious base or prove compiler correctness.

## Contracts that must move together

Keep restoration `:restored-precheck`; its format deliberately omits kernel
associations and published source authority. Add an explicit artifact admission
operation afterward. Do not turn a false flag true or manufacture a strict-check
certificate. Preserve strict `associate-checked` / `open-checked` meanings, or
deliberately generalize their contracts with distinguishable admission evidence.

Init prefix and subsequent imports must inherit the same base and check new
additions. `source_import.clj` currently rechecks the whole Init+A map; bypassing
only the initial strict check would leave that cost and its assumption unchanged.

Env supports pure external lazy lookup with soft caching and immutable local
additions. Lazy projection is a plausible later optimization, but `allConstants()`
enumerates only the local overlay. Base coverage requires the admitted source's
exact name inventory and its binding to the lookup view. Thread-confined resolver
policy and the backing lease also remain explicit. Eager projection is acceptable
for the first systematic implementation.

## Measurements and release placement

The current-cohort retained run restored in 89.3 s and freshly checked 65,994
constants in 180.7 s. Strict checking allocated about 239.5 GB cumulatively on
the caller thread; this is not retained memory. Guarded peak process-group RSS
was 3.46 GiB. Removing checking does not establish a subsecond startup or a
smaller heap: restoration and frontend preparation still need measurement.

Keep that passing strict run as release/cohort evidence. Implement a narrow
cohort-bound trusted-artifact provider for the bounded preview, test mixed
artifacts, changed guest maps and rejection of invalid new declarations, then
repeat genuine loading/edits/versions/callbacks/teardown through that profile.
Measure actual startup and heap before choosing defaults. StrictFresh remains
an explicit validation/audit mode. This is a justified release profile, not a
reason to wait for signing infrastructure or general checkpoint technology.

The fast profile is a planned release gate. Existing precreated stores or hashes
do not make it implemented. Continue ordinary development in the small REPL and
reuse a live provider across source experiments under its lease contract.

## Checked-delta experiment

`prototype.checked-delta` implements the live strict-base portion of this plan;
`research/checked-delta.clj` preserves the original REPL entry points. This does
not implement trusted-artifact admission or change provider defaults.

`capture-base` borrows a guest Environment whose positive kernel association and
actual strict verifier certificate already exist. The host supplies the current
authorized helper invoker and an independent admitted helper registry. Capture
checks the complete eager Java domain, guest enumeration, inherited checking
shapes, quotient flag, protected helper closure and backing source identities.
It returns the actual post-helper World and an opaque in-process capability;
serialized data cannot recreate that capability. Guest roots and source leases
remain owned by the host.

Java `ConstantInfo` has public mutable fields/arrays, and CONST expressions may
hold mutable universe arrays. Capture copies the CI array containers and records
the reachable expression universe arrays once, traversing the shared DAG by
identity. Extension checks compare the current Java objects and those arrays
against their snapshots before and after guest helpers. The host must serialize
operations and prevent concurrent mutation; these guards are not synchronization.

`verify-extension` takes that capability, the current authorized context and the
complete final guest ConstantInfo enumeration. It checks that inherited names,
references and checking shapes still match, then checks only new declaration
groups against the existing immutable Java Env. New assumptions and unsafe
declarations require explicit policy; inherited assumptions retain their original
admission. Inductive families and mutual definitions use the existing grouped
kernel operations. An unchanged import returns the same Java Env. The returned
certificate must still be associated with the exact final guest Environment;
this experiment does not publish that association or executable code.

Only eager bases and at most one open immutable module Store are supported.
Local inherited graphs are reprojected on each operation; immutable Store
projections can be reused under the existing source identity guards. Thus this
removes repeated kernel checking, not all inventory/projection costs. Errors
preserve the actual latest World, stage and outstanding helper owners rather
than authorizing replay of guest effects.

The retained 384 MiB REPL gate passes 12 tests and 88 assertions, covering new
definitions/proofs, assumptions, complete inductive and unsafe mutual groups,
inherited mutation/replacement/omission, source closure/shadowing, helper/binding
replacement, Java object/array mutation, quotient bootstrap and failures after
guest progress. Failure owners remain the caller's cleanup responsibility. The isolated Java baseline runner
also includes this gate. No full Init or Mathlib image is loaded for these tests.
Provider integration and genuine source acceptance under the faster profile
remain pending.

## Explicit delta finalization

`prototype.delta-import/finish-finalization` consumes an actual completed guest
finalizer IO.Result. It checks additions against the live strict base, projects
the genuine header's quotient metadata, and establishes the exact final guest
association. It never invokes the finalizer again. Selected helper closures and
raw bindings require independent identity authority before consuming success IO.
Guest IO errors return unchanged, with no helper execution.

`prototype.source-import` provides explicit `prepare-init-prefix-delta`,
`finish-over-init-delta` and `finalize-over-init-delta` entry points. A prepared
prefix retains its issued base capability; completion obtains the capability
from that authenticated prefix. The source receipt still covers precisely the
new module and rejects subsumption or changed inherited references. Existing
strict entry points remain available.

Progress-aware association/header helpers preserve the actual latest World and
outstanding owners after each returned helper and successful release. Child
failure owners and enclosing owners are separate credits, including repeated
aliases. They must not overwrite each other or be deduplicated. Diagnostic
pre-operation snapshots do not authorize cleanup against a newer World.

These are bounded integration APIs, not a switch of the resident provider to the
fast profile. Next: positive admission of a supported artifact cohort, explicit
provenance through resident/kernel publication, then genuine provider acceptance
and startup/memory measurements. Fresh strict replay remains the audit path.
