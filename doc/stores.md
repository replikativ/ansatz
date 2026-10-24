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

Opening an existing store selects its manifest's writer format. A format-1 writer
rejects extended full-CI hints instead of writing format-2-only values under a
format-1 manifest. Symbolic shells and ordinary maps remain supported. Unmanifested
stores default to format 2; an explicit `:write-format` cannot override an existing
manifest. Readers remain independent of writer selection.

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


## Bundled resource inventory

`ansatz/bundle.edn` records the exact six bundled resource paths and hashes.
Bundled initialization verifies and captures all six before activating proof state;
metadata loaders consume that captured snapshot. Lazy preludes require the active
bundled environment's cohort, and JAR/uberjar builds verify the copied staging
resources before archiving them.

This is a legacy byte inventory: kernel exports record Lean 4.29.0-rc2, while
metadata producer history and common generation remain unrecorded. Hash agreement
does not establish proof validity, authenticity, or Lean 4.33 frontend compatibility.
The former individual regeneration scripts now fail before writing anything;
changing resource bytes without updating a valid inventory is rejected.

An experimental schema-2 generator creates a separate six-resource candidate:

```sh
python3 scripts/generate-bundle.py --exporter-source /path/to/lean4export \
  --lean-root /path/to/pinned/lean/toolchain --output target/bundle-candidate
```

It pins Lean 4.33.1 and the exporter commit, captures their actual generation
inputs, rebuilds the exporter and Java checker in staging, checks public roots,
replays each kernel closure, compares overlapping declarations, and validates
selected companion rows. The final manifest is written last. Each role must close its own global
companion references before kernel replay; names exported only by another role
do not satisfy that gate. The shared metadata corpus is rendered only after all
three roles pass. Kernel raw files are captured once, decoded with strict UTF-8,
and those same bytes are compressed after checking.

Each staging directory is claimed atomically before validation work. The claim
stays after success or failure; another validation attempt refuses before parsing
or writing resources. Retry requires a fresh staging directory, preserving the
failed capture. The claim coordinates validator writers; it is not checking
authority or protection from arbitrary external filesystem writers.

Every owned parser store must close before candidate files are written. Final
manifest publication links a complete, closed staging-local temporary file into
its final name without replacing an existing marker; filesystems without that
operation fail closed. Validation, parser-close and precommit failures leave no
new final marker. A temporary-file cleanup failure after publication reports a
published outcome with a bounded retained-file diagnostic. This does not promote
or activate the candidate, or provide general input decoding budgets.

Public roots from
the legacy inventory require an explicit version migration when absent; private
generated names are reached through dependency closure. The generator never
ignores missing requested roots or installs the result into the repository.

The staged exporter applies the captured
`scripts/lean4export-structural-exprs.patch`: upstream's alpha-equivalence cache
can otherwise change emitted binder annotations with traversal order. The base
and effective source inventories are recorded separately, and the manifest
identifies the effective source hash. Full declaration overlap checks retain
binder metadata; the source checkout is not modified.

`validation.edn` distinguishes structural generation from consumer support and
records actual supplemental dependencies in the Init closure. Unsupported
unfolding or simp-phase fields remain preserved in staging but reject
activation. Generic attribute imports now reject the same unsupported semantics
before mutation, while retaining legacy absent-priority rows and four-element
persisted tuples. Existing stores do not require a tuple-format migration.

Promotion still requires active-environment companion coverage, including lazy
prelude admission and replacement targets, plus WF/SizeOf acceptance. The shipped
inventory remains schema 1; a staged candidate is neither a prepared frontend nor
a kernel proof certificate.

The first real 4.33 candidate passes all three kernel replays and exact overlap
checks, then fails companion closure: selected compiler replacements reference
declarations outside the seed closures. The first pass finds 23 missing attribute
targets, including four unsafe implementations. Completing that closure requires
an explicit runtime safety profile and metadata-derived roots, plus replacement
proof witnesses; it is not addressed by silently dropping rows or enabling unsafe
exports. No generated 4.33 bundle has been promoted.

## Scoped proof sessions

`ansatz.session/capture` returns a complete snapshot over the existing ProofContext:
Env, indexes, borrowed store descriptor, recall source, and tactic caches. Its
synthesis-cache atom is independent of the live atom. The record retains its
original three fields; capture adds the session fields as extension keys. Bare
`a/context` or `a/make-context` values remain useful for proof APIs but are not
complete snapshots accepted by `session/activate!`. For example:

```clojure
(require '[ansatz.core :as a] '[ansatz.session :as session])
(def saved (session/capture))
(def result
  (session/with-session saved
    (fn []
      ;; Run ordinary proof operations against this session.
      (a/env))))
(:value result)   ; callback result
(:session result) ; updated complete snapshot
```

Scopes restore the previous session on return or exception; nested scopes are allowed.
If restoration itself fails, an existing error is preserved with any distinct
restoration error suppressed; otherwise the restoration error is reported directly.
The caller must inspect and repair the remaining state.
`activate!` installs a complete captured snapshot after validation and attempts
rollback if installation fails. Store handles remain borrowed and must outlive
all sessions using them. Catalogue connections are not resurrected; lookup uses
the restored source path and reconnects lazily.

A shared lock serializes these operations and session activation during initialization.
Unlocked definition
macros are still outside that concurrency contract. Sessions do not roll back
namespace Vars, host registries, arbitrary IO, or external effects. They are also
separate from the experimental guest Lean runtime contexts.
