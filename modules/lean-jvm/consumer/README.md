# Java application-JAR consumer

`ProjectSmoke.java` uses the actual public `Lean` / `LeanProject` facade with an
original Ansatz interop artifact packaged in its application JAR. Its source is
in `resources/lean/interop.zip`; the independent expected manifest hash is fixed
in the consumer and recorded in `resources/lean/interop.json`.

The fixture checks Nat at 0, 42, Long.MAX_VALUE, 2^64 and 2^200, exact Unicode/NUL,
checked-signature rejection, negative/malformed arguments without poisoning a
live Project, idle thread handoff, repeated captured IO Unit output and retained
handle invalidation after idempotent close. It also verifies that the source
compiler and legacy prototype namespaces never loaded. Its original source is
`Main` importing local `MathCore` and `Text.Core`, with `answer n = twice n + 1`,
`echo s = "Hello, " ++ s` and a main greeting. Init output follows the pinned Lean
Apache-2.0 cohort. No FP Lean tutorial content is packaged here.

Resolve the SDK plus Clojure 1.12.0, spec.alpha 0.5.238, core.specs.alpha 0.4.74 and
data.json 2.5.1 through ordinary Maven dependency resolution. Then, from the module
producer directory:

```sh
python3 consumer/project_check.py --sdk-jar target/ansatz-lean-jvm.jar --dependency-jar "$CLOJURE_JAR" --dependency-jar "$SPEC_JAR" --dependency-jar "$CORE_SPECS_JAR" --dependency-jar "$JSON_JAR" --output target/public-consumer
```

This producer/test script audits the actual SDK archive, compiles the Java test
with release 17, builds a separate application JAR containing its classes and
resources, then executes it from an empty working directory. The runtime
classpath is that application JAR and the five normal dependency JARs. It
contains no source directory, Python, Clojure CLI, Lean installation or runtime
javac. The runtime Java heap is 384 MiB. Python and javac are producer/test tools.

[sdk_audit.py](sdk_audit.py) audits the actual SDK archive against the reviewed
source inventory, compiled-class inventory, runtime resources and Maven dependencies.
Static rejection checks mutate real archive bytes, including self-inventoried
helpers, source relabeling, changed classes and dependency drift:

```sh
python3 consumer/audit_checks.py --sdk-jar target/ansatz-lean-jvm.jar
```

`JarSmoke.java` retains the initial lower-level adapter check. Run it with the same
`project_check.py` launcher and `--main-class JarSmoke` when checking the adapter
without the public Project facade. Published historical observations remain in
[validation.json](../validation.json) and [consumer receipts](receipts/).
Current candidate results belong in CI/review artifacts; see
[release checks](../RELEASE_CHECKLIST.md).

## General application-value consumers

`GeneralInteropSmoke.java` loads the original two-file
[common corpus](resources/lean/general-interop-source/Main.lean) from
`resources/lean/general-interop.zip`. It checks arity, all five core value types,
nested products/options/lists, Some Unit versus None, exact named IO dispatch,
argument refusal without losing a healthy Project, Clojure round-trips and close.
Its independent trusted descriptor is [general-interop.json](resources/lean/general-interop.json).

`ScalarInteropSmoke.java` loads the original
[scalar corpus](resources/lean/scalar-interop-source/Main.lean) from
`resources/lean/scalar-interop.zip`. It checks both float widths, wrapping machine
arithmetic, all machine integer widths, Unicode scalar chars, array/byte snapshots
and updates, Sum/Except, nested IO results and explicit range/type rejection.
Its descriptor is [scalar-interop.json](resources/lean/scalar-interop.json).
[Oracle.lean](resources/lean/scalar-interop-source/Oracle.lean) checks representative
results using official native Lean; it is producer test material.

Pass `--main-class GeneralInteropSmoke` or `--main-class ScalarInteropSmoke` to
`project_check.py` with the same five-JAR closure and a separate output directory.
Each resulting application JAR runs without a source compiler, Lean installation
or native helper, and asserts that the source compiler namespace never loaded.
The fixtures are native frontend evidence, not Java-kernel-checked declarations.

For the explicit native source gate, use the built SDK JAR and ordinary runtime
JARs on the classpath, run from this module, and provide a new output directory:

```sh
java -Xmx512m -Xss8m -cp "$CLASSPATH" clojure.main test/source_acceptance.clj \
  "$LEAN_SYSROOT" "$PRODUCER_BUNDLE" "$NEW_OUTPUT_DIRECTORY"
```

This gate observes actual compiler cache results and issued build receipts. It
checks cold/cache/edit/reload/artifact paths, both corpora, warnings and errors,
unsupported capabilities and higher-order entry rejection. It changes only its
new owned output directory. The v2 candidate helper bundle is required; no download
or installation is performed. The mandatory JVM-only CI gate needs no toolchain.
