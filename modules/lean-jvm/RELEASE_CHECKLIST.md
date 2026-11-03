# Lean/JVM release checks

Review the supported scope and documentation before merging or publishing a
release. Main automatically publishes coordinated core and optional SDK artifacts;
merging is a release step.

## Acceptance

Run `bin/run-lean-jvm-checks` from the repository root. It builds the SDK and
checks source capture, the packaged-JAR suites, archive tampering, application-JAR
consumers, managed ownership, numeric behavior and resource limits. The consumers
must use the SDK plus its ordinary dependency JARs without source directories or
native tools on their runtime classpath.

With the pinned native toolchain and supported producer bundle supplied explicitly,
run both native gates documented in [consumer checks](consumer/README.md) and
[preparation](PREPARATION.md). Cover cold/cache/edit/reload/artifact loading,
frontend diagnostics, unsupported types/capabilities, both public preparation APIs
and CLI refusal to replace an existing output. Run the scalar corpus's
[official Lean oracle](consumer/resources/lean/scalar-interop-source/Oracle.lean).
Review the supported carrier, import and IO limits in [the SDK guide](README.md).

For supplied-stdio changes, also run the native differential/source/artifact
gate in [STDIO.md](STDIO.md). Verify finite input, exact raw captures, malformed
UTF-8, repeat invocation, limits and expected admission refusals. The JVM-only
gate must include the prepared stdio application-JAR consumer. Keep the
[compatibility ledger](COMPATIBILITY.md) aligned with completed evidence.

Record the exact candidate JAR/POM, producer archive identity and observed checks
as review or CI artifacts. Keep historical validation/source receipts unchanged;
they do not validate a new candidate. Audit documentation examples, local links,
producer source hashes and attribution before release.

## V3 datatype acceptance

Preserve old v1/v2 carriers, metadata refusals and artifact compatibility. Check
native-derived `LeanType` descriptors, all constructors and scalar lanes,
nominal/builtin nesting, `Option Unit`, immutable bytes, explicit materialization,
source reconciliation and defining-product custody. Changed defining products,
wrong identities, malformed host fields and unsupported families must fail.

Run the independent three-file [datatype application](examples/datatypes/README.md)
through public Java and Clojure calls, including transformation, records, custom
IO payloads and reuse in a new Project after close. Check aggregate input budgets
before execution, healthy reuse after host refusal, shared certified payloads,
and the existing terminal policy after guest IO failure. Compare the four-type
oracle fingerprints with genuine native captures. Run the isolated nominal
application-JAR consumer, the independent native oracle example and the full
engine contract gate before marking acceptance complete. Local implementation
checks do not replace these gates or establish a performance claim.

## Publication order

The published v1/v2 bundles retain their supported scopes. The independently
pinned v3 producer is published separately with its source closure and build
receipt; its [publication record](producer/candidate-v3.json) records the exact
archive. Source support must be checked against those actual bytes before
landing. Main automatically publishes coordinated SDK artifacts; the user's
landing authorization includes that consequence. FFI is a later design discussion.
Use the actual coordinated release version; do not assign a release claim from
a local build. The deployment job must verify and publish the exact checked JAR/POM
bytes without rebuilding them.

## Simm.is launch article

After release completion, prepare the requested Simm.is article and keep it
unpublished until SDK/producer versions and download links are verified. Show:

- Why a JVM application calls Lean, with a diagram separating core Ansatz, the
  optional SDK, native frontend preparation and JVM-only deployment.
- The pinned, unchanged FP Lean insertion-sort module and its explicit IO
  adapters, source loading and captured output from Java and Clojure/Superficie,
  with attribution. Distinguish its size/termination proofs from a sorting proof.
- Artifact preparation and JVM-only deployment with a trusted manifest hash.
  Show only examples actually executed against the released artifact; the
  general interop corpus separately exercises several arguments and nested types.
- Editing/reloading a new Project, explicit old-handle cleanup and the tested
  import/type/IO limits. Keep future frontend hosting, kernel import, public forks
  and specialized JIT work separate from current product claims.

Use the website's existing Clojure/Superficie tabs, with Clojure forms as the
single source. Execute every article example against the exact released JAR,
check form equality and the upstream tutorial pin, then build and review the
website article and code tabs before publication.
