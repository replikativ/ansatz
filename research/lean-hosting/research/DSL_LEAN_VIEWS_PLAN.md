# Versioned Lean views for the Ansatz DSL

Status: implementation plan after the genuine imported-function probe, not a
bidirectional public API. The probe used explicit Nat binders and an explicit
empty instance registry; it establishes shared logical declarations, not native
instance-search or simp parity.

Add a read-only `dsl-view` operation beneath the resident Context lock. Resolve
the current admitted kernel association through protected helpers. Return an
owned matching Context plus an immutable Java Env metadata overlay and an opaque
process-local view identity bound to guest environment/root/constant-map,
source-unit version and the supported scope snapshot. Do not create a new kernel
association just because `env/with-extension` produced an overlay.

The first bounded view can expose exact structural Names, declarations and
explicit Nat/String terms, with unsupported implicit-search/attribute features
reported explicitly. Avoid global `ansatz-env` resets and global attribute
installers; use immutable Env extensions. A retained old view must continue to
denote the old declarations and metadata after a Lean reload.

## Metadata transport

Use separately pinned typed guest helpers to export actual native metadata from
the same live environment. Bundled/store registries are not substitutes for that
view. If a required command/scope state is not retained by the frontend protocol,
extend the protocol or reject that scope-sensitive profile explicitly.

Native instances carry discrimination keys, values, priorities, erasures, active
scopes and synthesis order. Export effective native tree order, not an unordered
instance-name map or sorted names. Existing `dump_instances.lean` intentionally
collects module-global registrations and ignores scoped entries; it is not a live
session snapshot. Ansatz's per-class candidate vectors are a search
representation, not a proof of native discrimination-tree equivalence.

Native simp state also includes pre/post phase, inversion/origins, priorities,
erased origins, unfolding and equation registrations. Existing attribute parsers
reject unsupported native semantics; preserve those rejections. Do not remove
fields to make an importer accept them. Derived simp indices must be view-bound,
or initially use a bounded eager local registry.

Transport structural Names. Existing string/TSV formats require a demonstrated
roundtrip for the admitted names or a new lossless installer. Refresh metadata
after publication while retaining earlier immutable views.

## Publication and acceptance

Logical publication encodes checked Expr declarations into a successor guest
environment and extends its actual Java association. Theorems then become usable
as proof constants. Executable publication additionally compiles the new
definitions and establishes the matching executable/source authorization; a
checked Java Expr alone does not make a runtime function callable.

Acceptance order:

1. Load a genuine Lean theorem and use it in an Ansatz proof; kernel-check the
   resulting term in the exact view.
2. Publish an Ansatz definition/theorem into a successor guest environment and
   consume it from a subsequent Lean file. Preserve universes, Names, safety and
   assumptions; keep logical and runtime-code publication separate.
3. Check old/new/old views, forks and scope changes for retained-version behavior.
4. Compare priorities, equal-priority order, erasure and supported simp behavior
   with native observations. Unsupported semantics must reject explicitly.

The public Java kernel/store facade can consume the same view/lifetime boundary;
it should not expose mutable checker internals or invent a second environment
authority. See [Java API strategy](JAVA_API_STRATEGY.md) and the
[hosting campaign](LEAN_HOSTING_CAMPAIGN.md).
