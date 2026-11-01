# Java-only jar consumer

`JarSmoke.java` is the actual Java consumer accepted against the initial built
packaging jar. It requires the canonical Clojure namespace as a jar resource,
resolves the precompiled interpreter, executes an explicit call returning 37,
reuses the engine for a call returning 42, closes it, and checks that neither
legacy prototype namespace nor old `ansatz.lean` backend was loaded. It is test
code, not a public Java Project API.

`check.py` accepts one SDK jar and four already-resolved runtime dependency jars.
The script audits archive contents, Java 17 bytecode, runtime metadata and exact
POM dependencies. It compiles the test consumer with `javac --release 17` and
runs it with a 192 MiB Java heap from an empty working directory. The consumer
classpath consists only of those five jars and its compiled test classes. It
contains no checkout directories, Clojure CLI, native compiler or runtime javac
inside the SDK. Python is producer/test tooling, not a runtime dependency.

From the module directory, set CLOJURE_JAR, SPEC_JAR, CORE_SPECS_JAR and JSON_JAR to the
Maven-resolved Clojure 1.12.0, spec.alpha 0.5.238 core.specs.alpha 0.4.74 and data.json 2.5.1 jars:

```sh
python3 consumer/check.py --sdk-jar target/ansatz-lean-jvm.jar --dependency-jar "$CLOJURE_JAR" --dependency-jar "$SPEC_JAR" --dependency-jar "$CORE_SPECS_JAR" --dependency-jar "$JSON_JAR" --output target/consumer-reproduction
```

Output contains portable result/hash metadata and stage stdout/stderr files.
The script does not resolve dependencies, publish artifacts or start Lean.
To audit only, omit dependency jars and add `--audit-only`; this starts no Java
process. An optional `--expected-engine-source-sha256` binds the jar metadata to
the accepted source inventory. A digest comparison is not source authentication.

```sh
python3 consumer/audit_checks.py --sdk-jar target/ansatz-lean-jvm.jar
```

The static checks use actual archive bytes plus deliberately invalid copies to
reject missing adapter resources, old runtime namespaces, duplicate engine
entries, leaked Java sources, dependency drift and a wrong engine source pin.
Their temporary artifacts stay under this module's target directory.
