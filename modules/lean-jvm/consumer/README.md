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

`JarSmoke.java` and `check.py` retain the lower-level adapter check from the initial
packaging acceptance. Its initial receipt remains historical; current archive
checks inventory all canonical sources, Java facade classes, codec and attribution
resources and both runtime POM dependencies. Static rejection checks use real
archive bytes plus deliberately invalid variants:

```sh
python3 consumer/audit_checks.py --sdk-jar target/ansatz-lean-jvm.jar
```

The root ran this application-JAR consumer successfully with the reviewed
engine, then ran the complete SDK CI launcher: 57 model tests / 245 assertions,
actual archive plus six rejection cases, public application JAR and 41 resource
checks all passed. The [observed candidate receipt](receipts/public-consumer-candidate-v1.json)
retains its actual JAR hash and false pre-acceptance marker. Acceptance changed
only that metadata marker afterward; final coordinated release hashes belong to
the release preparation receipt. [Source](receipts/source-api-v1.edn),
[lifetime](receipts/lifecycle-v1.edn) and external tutorial receipts record
separate observed gates. Producer checks do not publish artifacts or submit
external forms.
