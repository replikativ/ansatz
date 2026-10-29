# Full Init artifact profile and resident/provider route

Read-only implementation research, 2026-10-28. **The full Init profile and its
provider integration are pending, not implemented or accepted.** The existing
17-CI fixture demonstrates the generic artifact kernel boundary; it is not a
supported full Init image. See [ARTIFACT_KERNEL_ASSOCIATION.md](ARTIFACT_KERNEL_ASSOCIATION.md)
for the implemented association, delta, provenance and witness contracts.

This proposal concerns explicit admission of an authenticated kernel base.
Ordinary Init store trust and existing defaults are separate concerns. This
document neither changes those defaults nor claims that normal Init loading
requires fresh proof replay.

## Authenticated input cohort

The historical `target/java-pure-provider-pack-v1/launch.edn` and `contract.edn`
identify these inputs. Paths below are pack-relative identities, not host paths.

| Input | SHA256 |
| --- | --- |
| `checkpoint/manifest` | `a848092bdd6753f2737a954907747e1bad900c11506ad371fcb8460b576c46d6` |
| `checkpoint/data` | `26282492007e48f6ba06466f0dea2c203c62d918da5ca283aee2db30449e773f` |
| `resource/full-init-module-data-v1/source` | `d3563f566d0eb70b76b4b7d148d7e28ee6f8464ad856288d762ffbb22bdff8d9` |
| `resource/full-init-module-data-v1/descriptor` | `62b168762b4ef900ac783589d4e8b4df4fa4712f120722190fbe4b3cfc0de144` |
| `resource/full-init-module-data-v1/index` | `148b2b9aecaf8b8b4bfd856b92b1ca3f85246ac7b40303ae035538b3878e3b1c` |
| `producer/archive` | `21acd0e8e735f46232dcb64ea3071600a2b2b0973167d46517e91b0db58b8129` |

The completed checkpoint and producer bootstrap archive serve different roles.
The archive header describes a frontend bootstrap with 311,523 functions,
124,194 heap entries and 50,320 globals. It alone does not authenticate the
completed finalizer map. The separate checkpoint manifest and data pins bind
that completed World and its actual successful finalizer IO.Result.

Bounded metadata inspection established:

| Item | Value |
| --- | --- |
| Lean version / commit | `4.33.1` / `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| Runtime target | `x86_64-unknown-linux-gnu`, 64 bits |
| Checkpoint manifest bytes | 38,564 |
| Completed checkpoint data bytes | 610,021,608 |
| Restored functions / heap / globals | 334,467 / 776,060 / 56,125 |
| Restored imported declarations | 13,003 |
| Successful IO.Result guest ID | 14,431,926 |
| Native resource base / node count | 352,932 / 11,233,359 |
| Source bytes / index bytes | 1,858,263,589 / 494,267,796 |
| Effective modules / transported roots | 631 / 3,155 |
| Actual completed Init declaration count | 65,994 |
| Historical explicit axiom assumptions | 15 |

Guest IDs are observations of this exact saved checkpoint, not portable
identities across independent worlds. Historical acceptance and measurements
do not establish acceptance of a new consumer source/class cohort.

## Select the actual restored map

Raw ModuleData concatenation is not the finalizer's constant map. Descriptor
counts give 170,384 CI occurrences across all 1,893 main data parts, and 66,124
occurrences across the selected private last parts. The actual finalized map
has 65,994 declarations. These counts establish merging; they do not establish
whether every duplicate occurrence shares the same CI reference or which
distinct occurrence native subsumption selects.

The new operation must enumerate the actual Environment from the authenticated
completed IO.Result. It must not reconstruct the selection from a union,
implement a new subsumption rule, or reuse the fixture issuer's duplicate-name
rejection as a full Init selection algorithm. The manifest also reports
`nativeEnvironmentFinalized: false` for transported ModuleData; that flag is
about transport, not a replacement for the separately authenticated completed
checkpoint.

No additional inventory credential is required if the supported profile binds
the exact completed checkpoint and the operation receives its actual restore
return. A derived digest of typed names and source-relative CI IDs would be
useful audit/golden evidence, but it must not become an invented prerequisite
when the existing checkpoint already authenticates the selection.

## Positive admission from the actual restore return

Add an explicitly named admission operation, provisionally `admit-restored!`,
immediately after actual restore and host-only bootstrap support preparation,
before user guest execution. Its trusted controller retains the actual opaque
Factory, restore return, ResourceLease and independently prepared support by
identity. It authenticates the fixed supported profile against that Factory's
contract and the checkpoint/resource pins above.

The current restore result is a map, not an opaque origin token. Within the
existing trusted-host contract, a controller-private constructor may accept
the identity-held actual return. Caller-created flags, provenance maps,
`:strictly-checked?`, or adjacent diagnostic snapshots do not authenticate it.
If this becomes a public issuer that independently authenticates arbitrary
supplied returns, add a narrow issued restore-origin receipt bound to the
actual Factory, original World/IO and lease. That receipt is optional for the
private controller design; it is not a second kernel inventory credential.

`restore-consumer/restore!` already verifies checkpoint manifest/data bytes,
quiescence, the successful IO root and resource recipes. It reopens and checks
the exact Store, including source/descriptor/index pins and the already-open
private index inode, then invokes and validates the authenticated Factory.
Admission must reuse this attached Store and actual ResourceLease. Use
`module-store/describe-attached` to check identity, liveness and absence of
overlap/shadowing; do not reopen the source, restore again, or replay finalizers
or initializers. The caller continues to own the lease.

The admission operation should:

1. Validate the independent executable/binding authority for every selected
   root, constants, quotient and optional map helper before guest entry.
2. Consume the actual successful IO.Result once, preserving its Environment
   owner and latest session/checkpoint evidence.
3. Enumerate the actual map and require 65,994 unique names with every CI root
   inside the exact authenticated native Store.
4. Use `compact-kernel-projection/make-scoped-projector` to project those CIs,
   build the eager Java Env with `addConstant`, and capture Java witnesses.
   Perform no base proof replay and manufacture no checked base order.
5. Publish exact guest/projection correspondence through the neutral association
   core, revalidating authority and witnesses across helper boundaries.
6. Return an issued admission token, artifact-relative projection/result and
   explicit provenance. Keep `:certificate` for strict producers and never flip
   the restored `:strictly-checked? false` bit to claim proof checking.

All failures retain the actual latest World/session and outstanding owner
credits, including repeated aliases. Entry snapshots remain diagnostic
alternatives, not retry or cleanup permission. Existing guard segments and
artifact-relative additions keep the contracts in ARTIFACT_KERNEL_ASSOCIATION.

## Explicit resident and provider mode

Keep `resident-preparation/open-checked`, `resident-frontend/adopt-prepared`
and strict association inheritance strict. Add explicit admitted preparation
and adoption entrypoints. They authenticate the issued token and live ledger
lineage while retaining the existing catalogue, executable, binding, frontend
and guest encoder readiness checks.

An admitted Context must privately retain its mode and required admission
authority. Propagate its adopter through application-session reopening,
callback authorization, prefix preparation, release and branch retirement.
Existing prefix code privately retains `:certificate` and repeatedly invokes
strict adoption; changing only the first open call is insufficient. Share
internal mechanics where useful, but do not globally permit artifact lineage
through strict-named APIs.

`coherent-source-preparation/prepare!` currently requires its controller's
actual `:checked` state/result and reads `:certificate`. Introduce a separate
positive admitted state transition and shared preparation mechanics. Preserve
the actual strict state branch; do not insert an artifact map into its strict
certificate slot. The admitted prefix similarly retains its projection/token
under an explicit basis.

The finite JVM controller's A/B loads use `resident/load-source` directly,
but it still prepares, owns and retires an Init prefix and reopens/adopts
application branches. These are all integration points even before broader
source reconstruction or graph-import acceptance.

A separately authenticated contract mode must select the admitted route.
For a minimal compatibility mode, retain the seventeen stage slots but record
`:base-basis :trusted-artifact` and `:operation :artifact-admission` explicitly
in the initial stage evidence. The legacy `:fresh-init` slot name must not be
reported as fresh proof checking. Add an admitted facts gate; do not invoke
the existing fresh-strict Init facts gate with relabelled evidence. Existing
contracts and strict defaults retain their present interpretation.

## Companion authentication and validation sequence

The kernel pin authenticates kernel data only. The Factory/launcher separately
authenticate selected consumer source and Java classes, producer recipe/archive
function identities, the declaration CAS index and requested blobs, helper
source/IR, initializer witnesses and exact host bindings. Retain that existing
authentication. No kernel admission token authenticates runtime/frontend
companions or grants source, executable or initializer authority.

Before a genuine full-source run, use small gates for wrong checkpoint/profile
pins; substituted World, IO, lease or Store; source closure/shadowing; incomplete
or nonnative CI selection; helper authority; late failure ownership and alias
credits; strict API rejection; admitted Context reopen/fork/retirement; prefix
retirement; and lineage after source callbacks. Model gates must stay labelled
as models rather than full Init/provider acceptance.

Regenerate a committed coherent source/class cohort using the existing tools
under `scripts/coherent/`, from `experiments/lean-ir`:

1. `materialize-cohort.py --repository REPOSITORY --commit FULL_COMMIT --output NEW_CAPTURE`
   captures committed source/resources without running JVM code.
2. `plan-java-build.py` takes that capture and its external digest, the pinned
   JDK release, the `/2` dependency lock and all thirteen ordered dependency
   pins, and emits a javac plan without executing it.
3. Run only the separately guarded javac command; retain its receipt/postcheck.
4. `observe-class-inventory.py` authenticates capture/build/receipt inputs and
   observes the complete fresh class inventory without compiling or running it.
5. `materialize-pack.py` consumes the new capture/build evidence, original pinned
   producer inputs, helpers, fixtures and explicit admitted contract composition.
   Its output remains review-required until source/contract/launch review.

See [PACK_PREPARATION.md](../scripts/coherent/PACK_PREPARATION.md) for exact
arguments and the existing dependency/classpath contracts. Keep original
artifacts intact; generated observations do not authorize their own launch.

After the small gates, source/class capture and contract review, perform one
guarded genuine full Init/provider gate covering artifact admission, actual
source elaboration/checking of additions, A/B selection/calls, callback effects
and managed disposal. Measure startup and heap separately from historical
fresh-strict runs. Full Init/profile/provider acceptance remains pending until
that actual new-cohort gate passes.

## Research limits

This document was prepared from source inspection, bounded checkpoint/descriptor
metadata, and existing recorded evidence. No JVM, restore, full image, full-source
scan, new proof check or provider acceptance run was performed for this research.
