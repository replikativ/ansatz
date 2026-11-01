# Canonical generated batches (M2)

This new unit consumes `general-command-receipt-v1/with-command!`. It leaves the
finite identity/arithmetic controller unchanged. Source-only implementation and
models are provided; no JVM, original compiler or generated code was run by this
worker. A successful command, executable batch, selected callable entry, and
reusable module remain separate capabilities.

Load the new general command issuer first, then `generated-batch.clj` and
`models/generated-batch.clj`, once in a quiescent process with their prerequisite
namespaces loaded. Run `(general-generated-batch-models-v1/check!)`. The models
replace Java linking and command custody explicitly. They are not substitutes for
an actual canonical Header / Java validator / original compiler probe. Do not
reload any issuer namespace while its opaque capabilities are live.

## API and authority

- `open-scope! driver adapter` borrows one actual engine/source/adapter and rejects
  inherited headerless functions. It issues only an opaque host metadata Scope.
- `prepare-batch! scope command-receipt` borrows the successful command through its
  issuer. The binding contains exact engine/source/adapter/current-context atom
  identities. The issuer checks actual source/version custody before and after
  the callback. Caller maps and supplied `verified` booleans cannot authorize it.
- `link-batch! batch` installs the privately staged final descendant once, only
  while the actual base Program and checked version marker remain unchanged.
- `close! scope` revokes all its batches and clears their host metadata. It does
  not retire a command or release any borrowed Source, Module, Run, store or guest
  occurrence. Failed install custody is quarantined; no VM unwind is claimed.

The receipt supplies complete immutable before/after/delta maps. Each typed Name
maps to `{:kind string :declaration original-IR-map}`; unsupported kinds remain in
the inventory. It also supplies its actual driver, source receipt, adapter,
checked version marker/id, and reviewed structural source-policy witness. This
witness must originate in the actual parser/gate/result protocol; an ordinary
fdecl body cannot prove absence of initialization/export/redirect requirements.
A terminal source command with a nonempty delta is not executable here.

A private per-file issuer marker is latched on the first receipt. Every accepted
receipt must have the next provider-validated command index, starting at zero
and bounded at 127. This rejects zero-code replay and mixing otherwise identical
empty intervals from different captured files. The marker is an ordinary private
host identity, not a Provider, CommandRun or CommandReceipt registry key.

The reviewed policy profile is `:observed-classic-prelude-command-v1`, with the exact
`:no-local-initializers-exports-externs-redirects-v1` requirements policy. Its custom
macro/effective-option frontier remains the provider's declared limitation. This
unit creates no extra source-policy or initialization authority.

## Staging and outcomes

Preparation verifies the entire old IR inventory is unchanged, bounds cumulative
local rows at 2048, and rejects typed Names that collide at runtime display labels.
Numeric and string Name components are preserved, never normalized together.
Every new fdecl is included, including arbitrary private compiler auxiliaries;
there is no boxed-name or kernel-CI-per-helper assumption.

The complete FnBody/Expr walk records unique direct FAP/PAP targets and every AP
path. Targets resolve to this batch, earlier linked local Headers, or the live
source-authenticated original resolver. All generated and direct-dependency
Headers are registered before the first body materializes, allowing SCCs. Each
materialization receives precisely its non-self direct Headers, and the existing
Java validator owns SSA/join/borrow/lane checks. Dynamic AP remains a recorded
frontier, using the ordinary runtime closure/boxed-ABI ownership guards.

Generated Header digests describe the captured original compiler row. They are
not original catalogue CAS identities. The common SourceBinding is used only
inside the scoped successful command borrow. Original dependencies retain their
independent authenticated resolver/CodeReceipt guards. No Host descriptor or
GuestExport policy is added, and `Program.extend` is never used.

Results distinguish `:empty`, `:unsupported` and `:prepared`. Unsupported rows,
dependencies, lanes or body preparation leave the engine Program untouched and
do not revoke the successful command. A later independent command can still be
processed; it cannot call an earlier unsupported/unlinked local as an original
source declaration. Successful linking stores canonical local rows/Headers for
later commands on the same scope. No entry codec or execution result is inferred.

The model cases cover whole-delta SCC staging, direct self exclusion, PAP and AP,
prior local dependencies, empty/unsupported commands, unchanged old rows,
source-domain/display collisions, fake receipts, source-policy absence, stale
versions/Programs, revocation, failed preparation/install and weak-registry
custody, zero-code replay and per-file command sequence. The scope stores a private pending marker instead of a Batch key; Batch
values store a private scope cell instead of a Scope key. Linked Batch values
drop the CommandReceipt. Closing a scope clears the remaining batch metadata.
