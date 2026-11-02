# Preparing a portable Lean artifact

This preparation interface is part of the current release candidate. It compiles trusted local Lean sources and exports a portable artifact without creating a JVM `LeanProject` or invoking that project's runtime initializers or `main`. The native Lean frontend can execute compile-time metaprograms and IO; preparation is not a source sandbox.

Preparation and execution are separate operations. The preparation process needs the explicitly supplied pinned Lean installation, supported native producer bundle, and writable cache. An application loading the resulting artifact needs the optional SDK and its Maven dependencies; it does not need those native tools, source files, or a compiler. See [producer configuration](producer/README.md) and the [supported source profile](README.md).

## Java

Reuse `ProjectOptions` to select the root module, source subdirectory, and checked entries. Native v2 signature discovery uses `.function(name)`. With a v1 entry producer, use the existing `.natFunction(name)`, `.stringFunction(name)`, and `.main(name)` selections instead.

```java
import ansatz.lean.jvm.*;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;

NativeCompilerOptions compiler = new NativeCompilerOptions(
    Path.of(leanSysroot), Path.of(producerBundle), Path.of(cacheDirectory));
ProjectOptions options = ProjectOptions.builder(compiler)
    .rootModule("Main")
    .function("increment")
    .function("main")
    .build();

PreparedArtifact prepared;
try (OutputStream output = Files.newOutputStream(
        Path.of("app.lean-jvm.zip"), StandardOpenOption.CREATE_NEW)) {
    prepared = LeanPreparation.prepareProject(Path.of("lean-src"), options, output);
}
String trustedManifestSHA256 = prepared.manifestSHA256();
String archiveSHA256 = prepared.archiveSHA256();
```

For example, `lean-src/Main.lean` can contain:

```lean
def increment (n : Nat) : Nat := n + 1

def main : IO Unit := IO.println "Hello from Lean"
```

`PreparedArtifact` contains digest values only. It holds no compiler receipt, interpreter, runtime project, or open stream. Keep `manifestSHA256()` separately in trusted application configuration and pass it to `Lean.loadArtifact(input, expectedManifestSHA256)` later. Reading a hash from the candidate archive itself does not establish independent trust. `archiveSHA256()` covers the ZIP bytes emitted by this preparation call.

The caller owns the supplied `OutputStream` on success and failure. Export finishes and flushes its ZIP but does not close that stream. Supply a fresh sink; a failed write can leave partial bytes, and the stream overload does not manage file replacement or deletion. Native compiler custody stays live through export validation and is retired before the method returns. Ordinary failures use bounded `LeanException` details; fatal host `Error` identity and interruption handling follow the existing Java facade policy.

## Clojure

`prepare-project` takes a source directory, the existing options map or a `ProjectOptions`, and a caller-owned output stream. It does not take a `Lean` runtime.

```clojure
(require '[ansatz.lean.jvm :as lean]
         '[clojure.java.io :as io])

(def description
  (with-open [output (io/output-stream "app.lean-jvm.zip")]
    (lean/prepare-project
      "lean-src"
      {:compiler {:sysroot lean-sysroot
                  :producer-bundle producer-bundle
                  :cache cache-directory}
       :root-module "Main"
       :entries ["increment" "main"]}
      output)))

;; Persist this outside the artifact as trusted application configuration.
(:manifest-sha256 description)
(:archive-sha256 description)
```

The returned map contains those two digest strings, with no native receipt or runtime state. `with-open` above is the caller's explicit ownership choice.

## Command line

The SDK includes a precompiled Java entry point. Put the SDK and its four resolved runtime dependency JARs in `lib/`, or supply an equivalent application classpath. No application `javac` step or Clojure CLI is needed for this form:

```sh
java -cp 'lib/*' ansatz.lean.jvm.LeanPreparation \
  --source ./lean-src \
  --sysroot "$LEAN_SYSROOT" \
  --producer-bundle "$LEAN_PRODUCER_BUNDLE" \
  --cache ./.lean-jvm-cache \
  --root-module Main \
  --entry increment --entry main \
  --output ./app.lean-jvm.zip
```

For a Clojure application with the optional SDK dependency already configured, the equivalent entry point is `clojure -M -m ansatz.lean.jvm.preparation` with the same arguments. `--help` lists the supported flags. `--source-root` optionally selects a relative source subdirectory; `--nat-function`, `--string-function`, and `--main` select legacy checked profiles.

On success stdout contains one JSON object with `manifest-sha256` and `archive-sha256`. On ordinary failure stderr contains bounded JSON diagnostics and the process exits nonzero. The reusable Java API and `cli-status` driver do not terminate their caller's process.

The CLI never replaces an existing destination. It prepares a sibling temporary file, closes it, then publishes the completed file using an atomic no-replace hard link. This requires hard-link support on the output filesystem, alongside the existing Linux native compilation profile. Temporary-file cleanup is attempted on success and failure. The stream API remains available when an application supplies its own storage transaction.

## Validation boundary

Preparation collects native checked-entry, module, and ordinary-startup evidence. Export revalidates the actual issued receipt and captured files before returning digests. It does not claim Java kernel checking, execution readiness, runtime intrinsic coverage, successful initialization, or a successful `main` call. Those checks happen when a later `loadArtifact` opens a JVM project and when an admitted function is invoked.

Selection is bounded by `ProjectOptions.MAX_SELECTED_ENTRIES` and the existing source, byte, dependency, code, and resource limits. Raising the entry count does not bypass those independent budgets. The source profile remains the documented pinned Init-plus-local-module DAG, rather than unrestricted Std/Lean/Mathlib/Lake imports. Unsupported types, binders, signatures, or execution capabilities still fail explicitly.

Focused models are in [preparation_api_checks.clj](test/preparation_api_checks.clj). They exercise stream/compiler lifetimes, errors, CLI publication, and ZIP failure cleanup with explicitly mocked native authority seams. Root-owned integration acceptance separately prepares actual source through the built Java/Clojure APIs and loads/calls the resulting artifact; models alone do not establish native acceptance.

The explicit native integration gate runs from this module against the built SDK
JAR and its four runtime dependency JARs (not the source directories):

```sh
java -Xmx192m -Xss8m -cp "$SDK_CLASSPATH" clojure.main test/public_preparation_acceptance.clj "$LEAN_SYSROOT" "$PRODUCER_BUNDLE" "$NEW_OUTPUT_DIRECTORY"
```

It prepares a two-file project with 35 selected functions, calls all 32 arithmetic
entries, checks mixed nested carriers and captured IO, and loads artifacts from
both public preparation interfaces. Source compilation retains its monitored
native memory admission floor; the Java heap limit does not cover native helpers.
