# Internal JVM compile/cache backend

`native-project-compiler-v1` ports the selected tutorial's compile/cache orchestration into Clojure/JVM code. It invokes the pinned native exporter directly through ProcessBuilder. The default Loader path invokes no Python. This is an internal research implementation, not a new public Java API, generic project loader, hosted Init importer or Java kernel checker.

Select the backend when configuring the Loader, before compilation or guest execution. New Loaders default to `:backend :jvm`; `:backend :python` explicitly selects the older prototype. Already-issued Python Loaders keep their original identity. No failed operation switches backend or replays the entry.

The JVM backend accepts the same four immutable source/TOML hashes. It captures bytes privately, validates them again before publication, compiles Greeting.Basic → Greeting → Main, preserves actual local initialization plans/roles and exports main's static closure. The existing runner independently authenticates and prepares the resulting `native-compiled-project/1` artifact; compilation does not itself issue a guest engine or type-check certificate.

The configured official toolchain/cache remain trusted inputs. The compiler checks the actual exporter binary, reported Lean commit/version, executable hashes and installed Init file stat inventory before/after compilation. These are ordinary mutation/provenance guards, not full library byte attestation. The new cache key includes this JVM implementation's source digest, so it does not silently reuse a Python implementation's key. Artifact format and runner admission remain shared.

That implementation record reads bounded source bytes from a real file or a bundled `file:`/`jar:` classpath resource. A packaged backend must include its compiler source resource; compiled classes alone are not this research package. Network source URLs are rejected.

Cache entries are immutable. A private build tree receives only captured source bytes; no project file is written. Every artifact file is hashed, the complete manifest is written last, and the directory is published by an atomic move under the cache root. Hits revalidate the input descriptor and complete bounded file set. A concurrent winning entry must revalidate independently. Failed/unpublished directories and actual process journals stay available for diagnosis; they are not reported as completed builds.

## Linux process profile

The internal launcher uses an explicitly configured `:resource-launcher`, or resolves `prlimit` from absolute installed PATH directories. It records that executable's identity. This research Linux dependency is not a public packaging promise; the release design can bundle an equivalent platform launcher.

Each child gets hard limits of 90 CPU seconds, zero core-file bytes and 32 MiB per output file. The JVM additionally monitors 900 MiB aggregate RSS across the root and observed owned descendants, 120 wall seconds, a 2 GiB MemAvailable floor and bounded stdout/stderr. The sampled process set is bounded to 64 handles; observed descendants remain journaled if their parent exits, and a surviving observed descendant prevents success. Sampling is not a kernel-enforced aggregate memory limit. Process construction is shell-free and single-threaded. A low-memory preflight stops before native start. Actual process handles are journaled before waiting; cancellation stops the observed owned process tree, preserves interruption and does not create or unwind a guest engine.

Even a cache hit currently probes the installed native toolchain version, so it respects the same process floor. Below that floor, do not spin or substitute old metadata. The compiler scope serializes its own calls; scheduling multiple configured compilers still belongs to the caller.

## Validation checkpoint

The parent definition-loaded the new namespaces in its existing JVM and ran seven pure metadata/cache/mocked-process families: 30 assertions, zero failures/errors. The external report is `target/java-source-exchange-v1/native-jvm-compiler-models-v1.edn`, SHA-256 `038e653ea7b924887c5230dd1f0ba095a6feb74a9585191eac4d7fb6d09e5398`. These tests launch no Lean, Python or extra JVM process and do not manufacture native-build authority.

Actual cold compilation, JVM-backend cache hit and entry execution through this new backend remain pending resource availability and source review. The earlier Python-service cold/hit and Loader cache-hit execution remain separate historical evidence. No new Compiler token or native job was required for the model gate. The loaded opaque Compiler namespace must not be reloaded beneath live tokens.

The second parent gate passed nine families and 38 assertions after the disk/JAR source-record and aggregate-RSS fixes. Its receipt is `target/java-source-exchange-v1/native-jvm-compiler-models-v2.edn`, SHA-256 `d9decb18d31c20174b4e580064d215cd9e7cbd494534d4918168be037b968b8a`.

The first actual compiler attempt then stopped before native start: the installed JDK rejected `FileInputStream.available` while `slurp` read `/proc/meminfo`. Both process-evidence readers now use bounded buffered reads without that whole-file optimization. A tenth model covers exact reads, missing files and the extent bound; its parent gate and the actual retry are pending. The failed Compiler is terminally retired before source descriptors are refreshed and a new Compiler is issued.
