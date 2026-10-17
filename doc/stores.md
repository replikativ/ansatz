# Publishing a store

A store is published **per import**, never per ansatz release. Its identity is

    <name>-<library tag>-f<store format>[-r<revision>]      e.g. mathlib-v4.33.1-f1

- **library tag** — what was imported (`MATHLIB_TAG` in `scripts/setup-mathlib.sh`).
- **store format** — `ansatz.store/write-format` is the format new imports emit;
  `ansatz.store/readable-formats` is the set this build reads. Fetch selects the highest
  published readable format satisfying explicit consumer requirements.
- **revision** — bump when the same library and format are imported *again* because our
  importer changed (new derived state, a fixed registry, …).

The artifacts live in [replikativ/ansatz-stores](https://github.com/replikativ/ansatz-stores):
one release per store id carrying `blobs.tar.gz`, `catalogue.tar.gz`, `meta.tar.gz` (the
manifest and the Lean export inputs) and `store.edn` (the descriptor, with each part's
SHA-256). The repository's `stores.edn` is the **index**: it maps a store name and format to
the current id and its parts, and `ansatz.store.fetch` reads it at fetch time — which is what
lets a new import reach existing users with no ansatz release. The copy in
`resources/ansatz/stores.edn` is only the offline fallback.

## Procedure

```bash
./scripts/setup-mathlib.sh                      # import (or re-import) the store
./scripts/verify-mathlib.sh && ./scripts/verify-mathlib.sh retry   # it must verify
./scripts/publish-store.sh ~/.local/share/ansatz/stores/mathlib
```

`publish-store.sh` packs the store (`ansatz.store.pack`: deterministic `.tar.gz`, so the same
store always gives the same checksums), creates the release, and prints the index entry to
commit to `stores.edn` in the store repository. Until that commit lands nothing changes for
users; after it, the next `(a/init! "mathlib")` on a machine without the store fetches the new
one. A published release is immutable — re-importing the same library and format means a new
`-r<n>`.

Verify a store before publishing it. What is published is what every user runs.

## Consuming

`(a/init! "mathlib")` fetches when the store is absent. `ANSATZ_OFFLINE=1` refuses to,
`ANSATZ_STORE_INDEX` points at another index (a path or a URL), `ANSATZ_STORE_BASE` at another
host for the artifacts — a mirror needs only the same `<base>/<id>/<file>` layout.

## Reader compatibility and verification

New imports write format 2. This build reads formats 1 and 2, so existing format-1
Mathlib stores remain usable and discoverable without reimporting them. Format 2 marks
the extended full-`ConstantInfo` reducibility-hint encoding: regular height zero and
all UInt32 heights survive exactly. Format-1 full-CI integer hints retain their legacy
interpretation; information already lost by an old writer cannot be recovered by
changing a manifest. The symbolic `CIShell` encoding already existed in format 1.

`check-format!` establishes readable storage only. `check-compatible!` additionally
accepts exact `:branch`, `:store/format`, and `:artifact/cohort` requirements,
a `:provenance` key/value subset, and a required `:store/capabilities` subset.
Missing required metadata is incompatible. `fetch!` and `ensure-store!` accept these
constraints as `:requirements`; the packer preserves provenance/cohort/capabilities
in published entries. Fetch validates the unpacked manifest against the selected
format, requested branch, advertised metadata, and consumer requirements before
installation. Checksums detect changed parts relative to the index; the index itself
is a distribution trust boundary.

These checks do not independently verify declarations. Loading a prepared store
uses its existing declarations without checking every proof at startup. The recorded
[Mathlib verification](kernel-validation.md) remains evidence for that preparation;
binding evidence to exact artifact hashes, checker identity, and admission policy is
separate from schema compatibility. A serialized `:verified true` grants no authority.

Named loading does not imply that every name has a published download. A locally
prepared `init` store can be loaded, but the current public index publishes Mathlib,
not full Init. `(init!)` remains the bundled setup; no additional Init option matrix
is introduced.

## Frontend companions

Kernel stores, guest Lean ModuleData, and executable/runtime artifacts provide
different capabilities. A future release manifest will coordinate their exact
producer identities and hashes. Kernel PSS data alone does not reconstruct missing
macro implementations or persistent Lean extensions. Bundled Init, custom preludes,
attributes, matchers, and instances must form one generated cohort before being
advertised as matching a frontend release. Current bundled 4.29 producer headers
are not evidence of compatibility with the experimental 4.33.1 frontend.

The optional `:artifact/cohort` field is an exact matching constraint, not a signature
or proof that resources were generated together. This change provides metadata
plumbing; it does not regenerate bundles or publish a prepared frontend cohort.
