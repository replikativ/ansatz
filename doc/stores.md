# Publishing a store

A store is published **per import**, never per ansatz release. Its identity is

    <name>-<library tag>-f<store format>[-r<revision>]      e.g. mathlib-v4.33.1-f1

- **library tag** — what was imported (`MATHLIB_TAG` in `scripts/setup-mathlib.sh`).
- **store format** — `ansatz.store/store-format`, bumped on any incompatible change to the
  on-disk store. An ansatz build only ever fetches a store of the format it reads.
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
