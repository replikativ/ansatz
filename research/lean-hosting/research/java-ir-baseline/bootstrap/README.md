# Explicit Source4 bootstrap

This package consolidates the bounded explicit-Prelude research runtime.
It does not enable full Init, arbitrary project imports, a native scheduler,
dynamic libraries or source-module reconstruction merely by loading definitions.
The existing lower capability factories remain authoritative.

Supply an independently accepted profile SHA-256 and an explicit map from
string root IDs to directories. `artifacts/authenticate-profile!` hashes the
profile before parsing it, bounds metadata, verifies every declared file's exact
size and digest, rejects path escapes and symlink aliases, and checks each
declared directory's complete file set. The CAS is an explicit resource root;
its contents are authenticated by the existing catalogue/index and per-row
lookup. It is never recursively loaded or accepted by a directory Boolean.
Pinned source proofs may use an explicit portable blob archive through
`artifacts/source-reader`.

The profile is metadata, not a checking or runtime capability. Its artifact
paths are relative to supplied roots. Include the actual accepted catalogue,
runtime jar/source/build receipt, selected capture, all four source overlays,
matched Prelude pair/store, layout evidence, policy fixtures and upstream blobs.
`profile.schema.json` describes the envelope. There are no default target paths,
machine-specific checkout locations or implicit sibling repositories.

Load the reviewed `artifacts.clj` and `definitions.clj` namespaces first.
The profile's `definitions` list gives exact artifact ID/namespace pairs in
dependency order; each source is pinned like any other artifact. The loader
preflights the entire list before its first `load-file`, rejects namespaces
which already exist, and never reads/evaluates selected historical forms.
Ordinary Clojure/kernel classpath dependencies remain an explicit caller setup
requirement. Models are a separate list and are never run by loading.

Call `source4/authenticate!` with that Profile, the caller-owned actual jar
basis and a fresh journal. The six-class jar identity check rejects parent
delegation before any engine. The function opens the actual catalogue, verifies
the reviewed policy bundle, authenticates exactly four source overlays and
composes once. There is no temporary two-overlay receipt. The selected capture
has its own independently pinned outer manifest; every captured Header is also
compared with the actual original CodeReceipt/CAS row. Capsule maps are discarded
after metadata preflight rather than retained alongside the installer's parse.

`source4/open-parent!` derives early descriptors against the actual jar's Native
registry, authenticates required guest-export reservations, and uses the
existing cohort importer. Its SourceBinding factory runs once; actual task,
sharing, profiling, helper and native policies use their existing factories.
The pristine seed executes zero guest instructions. Original code warmup is
optional, metadata-only and reauthenticates every Name/SHA under this new source.
Generated file rows are never promoted into it.

Prepare the fixed matched Prelude once with `prepare-module!`, then use
`prepare-child!` or `open-file!` with an explicit immutable captured-source map
and fresh journal. The general512 driver is chosen before wrapper capture.
Original startup, finalization, Base and source observations are genuine lower
transactions; extra overlay lineage is passed explicitly. No `with-redefs`
or `compose!` interception supplies lifecycle evidence.
General FileRun loading/invocation/closing remains in the existing public
`general-frontend-file-v1` API.

Journals are published before resource/image effects. Do not put their own
Bootstrap token back into the mutable journal. Partial failures are terminal and
preserve actual owner/resource packets; these APIs do not invent rollback,
resume a failed interpreter or automatically discard a branch. Normal seed
retirement checks the actual privately latched child engines created through
this bootstrap are disposed and
closed, with journal receipts supplementary rather than authoritative. The
private latch is populated by the trusted production factory's actual child,
not a caller-supplied map. Retirement keeps services live through disposal, then
closes the cache/catalogue. Forks made directly through lower APIs require their
own independent lifecycle. The caller retains ownership of the input Profile
and jar classloader.

The parent completed one fresh 512 MiB bootstrap using profile
`3e1850867319b5220354a5ba307d1c3a303433070e4dfe5e41568dd96c22852b`:
all 47 tracked definitions, zero-instruction pristine parent, matched Prelude,
two strictly checked/compiled earlier-reference definitions and genuine EOF.
The linked boxed entry returned `40 -> 42`. File and parent retired normally,
then Profile and jar classloader closed; no ignored implementation loader,
original-code warmup or native Lean invocation was used.
[assembly-validation.json](assembly-validation.json) pins the actual report and
dependency-basis descriptor. This is one explicit Prelude file at 512 MiB, not
full Init or arbitrary project support. Historical acceptance remains unchanged.

The selected checkpoint's scalar decoding and logical-MT reconstruction remain
the explicit target import profile. Source RC records do not recover historical
native MT flags or native physical scalar layouts. Relocatable artifact locators
also do not rebind host-sensitive values retained inside captured state (for
example historical search paths). This first route admits only its explicit
Prelude/import policy; no arbitrary use of captured host resources is granted.
