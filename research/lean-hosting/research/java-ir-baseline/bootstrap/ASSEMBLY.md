# Explicit Source4 pack assembly

`assemble-pack.py` copies a selected immutable byte distribution. It does not
run Java, Lean, a catalogue, an importer, a policy configuration or a guest.
It does not infer inputs from a historical target directory.

The caller supplies an assembly-plan JSON and accepts its SHA independently.
The exact plan bytes are hashed and parsed together. Every input records its
expected SHA and byte extent, an explicit input root ID and normalized relative
path, and its normalized output path. Supply roots with repeated
`--root ID=CANONICAL_DIRECTORY`. Root paths belong in local invocation inputs,
not in tracked guidance.

```sh
python3 assemble-pack.py --plan assembly-plan.json   --plan-sha256 INDEPENDENTLY_ACCEPTED_SHA   --root inputs=CANONICAL_INPUT_ROOT --root lean=CANONICAL_LEAN_REPOSITORY   --output NEW_PACK_DIRECTORY
```

The output directory must be absent. Failed assembly leaves an unissued sibling
staging directory for inspection; it never overwrites an accepted pack. Successful
assembly publishes the completed directory with `profile.json`,
`assembly-receipt.json` and `runtime-build.json`. The receipt reports the exact
artifact count and bytes. Input and output hashes authenticate bytes; an operator
must still accept the resulting profile SHA independently before calling
`artifacts/authenticate-profile!`.

## Plan contract

Use schema `source4-pack-assembly/1` with exactly these fields:

- `profile`: the complete existing `ansatz-source4-bootstrap/1` profile template,
  omitting `artifacts`; `definitions` may be omitted because the assembler derives
  them from the checked order file. All directory groups have root `pack`.
- `inputs`: artifact-ID to `{root, path, output, sha256, bytes}`. No source
  symlinks, duplicate outputs or implicit directory contents are accepted.
- `runtime-build-artifact`: the ID referenced by
  `profile.runtime.build-receipt`, distinct from copied input IDs.
- `definition-order-sha256`: independently accepted digest of the tracked
  `definition-order.json`.
- `dependency-artifacts`: a nonempty list of copied artifact IDs recording the
  intended external Clojure/kernel dependency basis, lock data and component
  revisions. These records describe inputs; actual acceptance must also record the
  running process basis. Pinning Interpreter alone does not establish it.

For a required pinned Lean source blob, replace `path` with `git-path` and add
`commit`. The only accepted commit is
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The assembler reads that exact Git
object, checks its declared size before extraction and checks its expected SHA.
It never reads dirty checkout content as source proof.

Every definition path in the order metadata is an exact repository-relative
output path. Include all three `entry-namespaces` as artifacts; load those
bootstrap entry files once before `definitions/load-definitions!`. The remaining
47 files are ordered prerequisites, frontend core, runtime services, source-module
units, policies and Source4. External `prototype.*`, kernel and ordinary library
namespaces remain on the explicit dependency basis, rather than being discovered
or selectively evaluated by this tool. Optional model files are separate explicit
profile inputs; adding them consumes the same artifact bound.

## Accepted runtime receipt

The tool requires the previously accepted jar SHA
`ec44338dbe9e44fc2484c16d00addf46468a14919f66a5d55c01db431f43fbed`
and Java source SHA
`617e8e63247289ce8a03b0afcc7794b5de17fcaa6f0faf7365c88238b34e1bc2`.
It reads the actual Interpreter class header from that jar and requires major55,
then emits the supplemental `java-ir-runtime-build/1` receipt expected by Source4.
This is identity/ZIP evidence for already accepted bytes, not a new compilation
or a proof of the running JVM classpath.

## Selection and bounds

Keep the existing 512-artifact /512MiB aggregate bounds. The store selection is
its manifest plus307 blobs, excluding its irrelevant import log. The captured
import directory contains only the actual manifest, graph capsule and Header
candidates; captured source is a separate artifact. Each overlay directory
contains only its source, local IR and export receipt. One shared exporter binary
is a separate artifact. Policy families retain exact complete file sets; the
77 upstream source blobs are individually pinned. The authority layout group
contains only its two required authenticated files. The catalogue index file is
explicitly included alongside its manifest; the CAS root remains an external
content-addressed input rather than an eagerly copied catalogue.

The final emitted profile is still checked by the existing schema and opaque
Profile factory. The assembler does not issue SourceBinding, Module, Base, Run,
CommandReceipt or checked declaration authority. A copied normalized graph is
not an admitted runtime image, and model success is not fresh bootstrap success.

`python3 assembly-checks.py` runs seven synthetic metadata tests, including
independent plan hashes, changed bytes, symlinks, exact directory sets,
namespace mismatches and overwrite/path rejection. No runtime process is started.


The first selected metadata pack is recorded in
[assembly-validation.json](assembly-validation.json): 504 artifacts,
308,939,081 declared bytes, 21 directory groups and 47 ordered runtime
definitions. It fits the unchanged 512-artifact bound. The independently
reported profile digest and external assembly receipt pin that exact selection;
they identify that exact distribution. The parent subsequently authenticated
the actual Profile and completed the scoped fresh bootstrap recorded in that
validation file. The author did not launch a JVM. A standalone Python JSON-schema
check was unavailable because that optional module is not installed; actual
production Profile authentication passed in the parent's process.
