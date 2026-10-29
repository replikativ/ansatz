# Artifact-relative kernel checking

Implementation contract from the Astra architecture review, 2026-10-28.
The kernel-data issuer, strict-base delta routes, artifact association/delta
APIs, callback provenance and shared snapshot/helper checks are implemented.
Full Init cohort selection and explicit resident/provider adoption remain pending.

## Authority and representation

Use one opaque artifact admission token, trusted actual internal verifier
results, and explicit provenance on associations/results. A second issuance
registry for every extension is unnecessary: existing strict certificates and
the World ledger already assume trusted host code. Untrusted inputs are artifact
bytes, transported guest data, source/compiler output and executable selections.
A caller-created provenance map cannot replace an actual issued artifact token.

Artifact associations/results retain:

```clojure
:kernel-provenance
{:base-basis :trusted-artifact
 :artifact-admission admission-token
 :base-assumptions original-base-assumptions}
```

Strict producers record `{:base-basis :strict-fresh}`. Checked additions preserve
the original base kind; they do not upgrade it to strict. Keep `:new-order` for
groups actually checked by the extension. Preserve existing strict `:order`,
but do not manufacture a checked order for an artifact base.

## Entry points and dependencies

1. Share projection/container witnesses through
   `prototype.kernel-projection-snapshot`, and independent executable/binding
   checks through `prototype.helper-authority`. Neither grants admission.
2. Factor the existing progress-aware association operation into a provenance
   neutral exact correspondence core. Preserve complete domains, exact guest
   references/shapes, quotient checks, helper progress and owner credits.
   Keep strict-named wrappers strict.
3. Add `kernel-artifact/associate-admitted-progress` taking the current authorized
   context, World, guest Environment, helpers and actual artifact token. Inspect
   the token, check helper authority, establish exact correspondence and publish
   artifact provenance. Revalidate across this explicit helper boundary.
4. Add `checked-delta/capture-artifact-base` with the same token authentication.
   Keep the strict capture/verification route separate. Add an explicitly named
   artifact-relative verification route using the shared grouping/checker core.
5. Add explicit artifact finalization around the shared delta completion flow.
   Consume actual finalizer IO once and associate its actual checked extension.
   Source-unit/executable/initializer/lifecycle authorization remains independent.

The artifact issuer depends on the neutral correspondence/snapshot helpers;
delta checking can then depend on the artifact issuer without a namespace cycle.

## Repeated extensions and Java witnesses

Capture resolves the current positive guest-root association and requires the
same issued artifact token. It must accept checked descendants, rather than
requiring identity with the token's original Java Env. Build the current complete
projection from the ledger's Env, actual guest enumeration, inherited artifact
references, provenance and prior witnesses.

Carry persistent witness segments: the original artifact snapshot and snapshots
of only newly checked CI groups. Take new witnesses immediately after checking,
before guest publication; validate those new groups across publication helpers.
Header/map inheritance shares witness references unchanged.

At explicit admission/import/recapture boundaries, validate existing witnesses
before making replacement snapshots. Otherwise a mutation of an earlier added
CI could become the new baseline. Recapture may compact validated segments.

Do not enumerate all Init declarations or rewalk its Expr DAG on each callback
or application call. Hot execution retains O(1) association/lineage checks and
the existing trusted-host prohibition on Java CI mutation between boundaries.
Opaque extension tokens would not fix concurrent mutation or remove that contract.

## Propagation and strict defaults

Every association write must retain provenance and witnesses:

- `kernel-host`: header/map inheritance, existing roots, empty-base creation and
  successful callback publication, including generated inductive families.
- `source-import`: protected compilation roots, prefix authentication and source
  receipts tied to the actual association and exact source CI subset.
- imported correspondence and delta final association after header attestation.

Return the input association entry internally, rather than only its Env, so
callback publication cannot lose lineage. Empty bases get strict provenance.
Retain strict `inherit-checked-association`, `open-checked` and adoption contracts;
introduce explicit admitted preparation/adoption paths instead of silently
allowing artifact lineage through strict-facing operations.

Do not weaken the actual Init closure requirements to fit the 17-CI fixture.
The fixture demonstrates the generic kernel boundary, not a supported Init cohort.

## Bounded acceptance before a full image

Use the fixed fixture to test initial positive association; forged tokens;
altered/omitted/replaced guest CIs; quotient mismatch; valid and invalid additions;
recapture followed by another extension; unchanged-map header inheritance;
callback publication with a generated inductive family; mutation of an earlier
extension rejected on recapture; addition-only axiom/unsafe policy; strict APIs
rejecting artifact lineage; source lifetime/shadowing; helper authority; and
latest-World/owner packets preserving repeated alias credits.

Then admit a supported full Init cohort with authenticated matching frontend and
runtime companions, run genuine provider acceptance, and measure startup/heap.
Fresh strict replay remains an independent audit mode.

The bounded callback tests use actual Java declaration checking and captured
Lean encoding IR with modeled guest Environment publication. They cover generated
inductive CIs and check that callbacks never call the full-segment audit. A late
helper mutation test verifies exact result/root/map owners and the actual latest
World on failure. These tests do not substitute for genuine frontend acceptance.
