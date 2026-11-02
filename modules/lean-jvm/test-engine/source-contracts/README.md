# Source authority contract migration

This matrix accounts for the 21 source-authority groups in the former mandatory
Java-engine runner: indices 134–135 and 138–156 at commit `4ace73f0`.
Indices 136–137 are kernel verification groups and belong to the separate kernel
port. The former source files lived under `research/lean-hosting/test/prototype/`,
except `research.checked-delta-checks` under its Java-baseline research directory.
Their Git history preserves the original tests; this directory does not load them.

The SDK authenticates native source/artifact evidence and executes admitted IR.
It does **not** import checked declarations into an associated Java kernel
Environment. Similar identity checks at these boundaries do not establish that
the retired kernel-association or resident-frontend APIs remain supported.

## Current checks

`source_authority_contracts.clj` runs in the SDK packaged-JAR lane using the genuine
`consumer/resources/lean/interop.zip` capture and its independent checked-in
`interop.json` descriptor. It adds three cross-interface checks:

- An actually issued artifact receipt cannot become a native source receipt,
  source export, or ready startup capability; failed substitutions leave it valid.
- Caller byte-array mutation and stream closure cannot alter issued artifact
  facts; copying the descriptive payload does not create publisher authority.
- Two Projects loaded from identical bytes retain separate handle authority.
  A failed additional load and closing one Project leave its sibling callable.

These tests exercise current production entry points, with no mocked issuers,
private registry insertion, native process, store, or historical World runtime.
They do not prove native source compilation: the separately supplied toolchain
acceptance in `test/source_acceptance.clj` and
`test/public_preparation_acceptance.clj` covers that path.

The table uses these existing SDK test files (all under `test/`):
`publisher` = `ansatz_lean_jvm_publisher_models.clj`;
`artifact` = `ansatz_lean_jvm_artifact_models.clj`;
`startup` = `ansatz_lean_jvm_module_startup_models.clj`;
`lifecycle` = `ansatz_lean_jvm_lifecycle_models.clj`;
`capability` = `ansatz_lean_jvm_capability_models.clj`;
`producer` = `ansatz_lean_jvm_producer_checks.clj`;
`preparation` = `preparation_api_checks.clj`.
These focused models are labelled as models in their source. Actual public calls,
close/reuse and carrier checks also run through `consumer/ProjectSmoke.java`,
`GeneralInteropSmoke.java` and `ScalarInteropSmoke.java`.

## Old obligation to current coverage

“Archived” means the old mechanism has no current SDK equivalent and is not
claimed as retained coverage. It does not mean an SDK negative test reproduces
that mechanism. Engine fork, initialization, IO and native frontend foundations
remain separately owned by the direct Java engine contract port.

| Old index / namespace | Applicable current obligation and coverage | Archived mechanism / scope gap |
| --- | --- | --- |
| 134 `research.checked-delta-checks` | Exact inherited authority and no forged replacement: publisher `changed-source-body-or-dependency-refused`, capability `descriptor-is-bound-to-actual-program-and-canonical-headers`; actual peer isolation in this directory. | Checked kernel extensions, inductive/mutual/proof/axiom policy, quotient bootstrap and live helper owner journals are not an SDK feature. Independent kernel checking belongs to the kernel port; no delta association equivalence is claimed. |
| 135 `prototype.delta-import-test` | Failed publication cannot create another live authority: publisher issuer checks, preparation failure cleanup, and failed-load sibling isolation here. | Guest-finalized delta maps, late kernel association and checkpoint/alias-credit recovery are archived. |
| 138 `prototype.module-import-test` | Complete declarations and native callable/type identity: publisher closure/body/dependency/type checks; entry v1/v2 tampering tests; actual portable consumer calls. | Native heap hydration, bulk guest module import and associated checked Environment are archived. |
| 139 `prototype.source-import-test` | Source/type evidence cannot be replaced by a same-shaped description: publisher issuer/observation checks, producer original-build pairing checks. | Native-prefix registration, hybrid source-delta routes, source-subset kernel receipts and their fork registries are archived. |
| 140 `prototype.kernel-artifact-test` | Independent artifact pin and real opaque token: artifact `expected-hash-is-independent-and-verified-before-schema`, `exact-issued-artifact-identity-and-no-fake-source-export`; receipt-role substitution here. | Eager trusted kernel base, guarded borrowed kernel data and checking a declaration relative to that base are not portable SDK artifact support. |
| 141 `prototype.artifact-association-test` | No self-asserted profile or token authority: publisher artifact-profile/issuer tests and current actual-receipt tests. | Kernel artifact anchors, descendant checked deltas, inherited Java mutation witnesses and late association publication are archived. |
| 142 `prototype.artifact-host-test` | Publication and failure cannot substitute another caller's authority: preparation cleanup and actual sibling/handle isolation here. | Callback-generated kernel declarations, strict/artifact anchor lineage and checkpoint owner escrow are archived. |
| 143 `prototype.kernel-host-test` | Unsupported capability refusal and no guessed success: capability exact ABI/task/unknown-extern checks. | Guest callbacks into the independent kernel checker, generated source families and checked map anchoring are not SDK callbacks. Preserve independent checker semantics in the kernel port, not as claimed host integration. |
| 144 `prototype.source-import-authorization-test` | Same-shaped payload/handle cannot inherit authority: publisher typed-name collision checks and actual artifact payload/Project identity tests here. | Derived source-header views authorized by exact kernel constant-map identity and source-unit receipts are archived. |
| 145 `prototype.resident-artifact-test` | Artifact trust does not imply source issuance/readiness: artifact profile/issuer negatives and actual receipt-role substitution here. | Store leases, resident environment adoption, readoption/fork audits and late lineage checkpoints are archived. |
| 146 `prototype.resident-frontend-test` | Calls require the actual ready/live Project; same-digest peers do not share handles: actual tests here, lifecycle terminal/thread/lease tests, public consumer call/close checks. | Incremental hosted frontend load, deferred resident units, custom host encoders, extern rebinding and inspectable partial guest checkpoints are archived. |
| 147 `prototype.resident-preparation-test` | Phase flags do not create readiness: receipt/startup refusal here, startup sequence/order/tampering tests, lifecycle terminal checks. | Associated kernel Environment/options globals, dual context credits and borrowed store ownership are archived. |
| 148 `prototype.resident-binding-dependencies-test` | Independent actual executable/type identity: capability program/header binding; publisher body/dependency/type checks; producer cohort pairing. | Resident helper closure protection across adoption, fork and application extern extension is archived. |
| 149 `prototype.full-init-admission-test` | A description cannot issue an artifact/source/startup token: current receipt tests and artifact issuer tests. | Full-Init artifact factory, guest kernel-map association and its two-level alias owner recovery are archived; ordinary SDK startup is a narrower profile. |
| 150 `prototype.coherent-consumer-profile-test` | Independent pin before schema; exact source/class/cohort identities: artifact pin check, producer pairing/original-build checks, SDK external inventory/archive mutation gate. | World restore constructors, factory attestations and coherent full-Init composition are archived. |
| 151 `prototype.coherent-stage-guards-test` | Publication waits for readiness; malformed phase/sequence/unsupported capabilities fail closed: startup/capability tests and actual artifact-not-ready tests here. | Coherent restore stages, exact full-Init axiom sets and helper work/owner summary protocol are archived. |
| 152 `prototype.coherent-source-preparation-test` | Preparation uses actual issued compiler receipt and does not claim runtime readiness: public preparation models plus actual native preparation acceptance; artifact/source role substitution here. | Strict/artifact coherent factory admission packets and private restore lease phases are archived. |
| 153 `prototype.coherent-helper-value-test` | Owner lifetime gates execution and authority is not a substituted description: actual Project close/peer tests here and public consumer close checks. | Invoking a helper under coherent strict/artifact preparation bases is archived. |
| 154 `prototype.resident-admitted-init-prefix-test` | Artifact receipt alone cannot authorize another readiness phase: actual receipt/startup checks here. | Reusable admitted init-prefix forks, source projection lineage and native17-prefix adoption are archived. |
| 155 `prototype.resident-init-prefix-test` | Exact original owner remains required: current peer handle/lifetime tests and lifecycle serialized leases. | Resident prefix release/readoption, inherited registry owners and terminal guest packets are archived. |
| 156 `prototype.coherent-jvm-slice-test` | Public reopen uses independent manifest identity; failed load preserves existing Projects; preparation stays separate from execution: actual tests here, preparation models and both native acceptance scripts. | Coherent controller/factory dispatch, restore envelopes, prefix close ordering, cell mounts and pristine application cache composition are archived. |

## Verification boundary

The new namespace is loaded by `ci_checks.clj` and participates in its ordinary
failure/error and executed-test checks. Run `bin/run-lean-jvm-checks` for the built
SDK path. Native acceptance requires an explicitly supplied pinned toolchain and
producer bundle; it is not established by portable captures or host-only models.
The old group/test totals are provenance, not hardcoded acceptance thresholds.
