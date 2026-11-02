# Lean/JVM release checks

The general interop and preparation APIs are an unpublished release candidate.
Agree the supported scope and documentation with the user before merging or
publishing. Main automatically publishes coordinated core and optional SDK
artifacts; merging is a release step.

## Acceptance

Run `bin/run-lean-jvm-checks` from the repository root. It builds the SDK and
checks source capture, the packaged-JAR suites, archive tampering, application-JAR
consumers, managed ownership, numeric behavior and resource limits. The consumers
must use the SDK plus its ordinary dependency JARs without source directories or
native tools on their runtime classpath.

With the pinned native toolchain and candidate producer bundle supplied explicitly,
run both native gates documented in [consumer checks](consumer/README.md) and
[preparation](PREPARATION.md). Cover cold/cache/edit/reload/artifact loading,
frontend diagnostics, unsupported types/capabilities, both public preparation APIs
and CLI refusal to replace an existing output. Run the scalar corpus's
[official Lean oracle](consumer/resources/lean/scalar-interop-source/Oracle.lean).
Review the supported carrier, import and IO limits in [the SDK guide](README.md).

Record the exact candidate JAR/POM, producer archive identity and observed checks
as review or CI artifacts. Keep historical validation/source receipts unchanged;
they do not validate a new candidate. Audit documentation examples, local links,
producer source hashes and attribution before release.

## Publication order

Publish and verify the reviewed v2 native producer bundle first, then update its
[setup instructions](producer/README.md). Land the SDK only after its acceptance
and the user's scope/release discussion. Use the actual coordinated release
version. The deployment job must verify and publish the exact checked JAR/POM
bytes without rebuilding them.

## Simm.is launch article

After release completion, prepare the requested Simm.is article and keep it
unpublished until SDK/producer versions and download links are verified. Show:

- Why a JVM application calls Lean, with a diagram separating core Ansatz, the
  optional SDK, native frontend preparation and JVM-only deployment.
- The pinned, unchanged three-file FP Lean tutorial, its import graph, source
  loading and captured output from Java and Clojure/Superficie, with attribution.
- A separate original example with several arguments, Bool and a product/Option
  result; artifact preparation and JVM-only deployment with trusted manifest hash.
- Editing/reloading a new Project, explicit old-handle cleanup and the tested
  import/type/IO limits. Keep future frontend hosting, kernel import, public forks
  and specialized JIT work separate from current product claims.

Use the website's existing Clojure/Superficie tabs, with Clojure forms as the
single source. Execute every article example against the exact released JAR,
check form equality and the upstream tutorial pin, then build and review the
website article and code tabs before publication.
