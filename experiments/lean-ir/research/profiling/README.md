# Small restored-IR profiling in a REPL

These helpers are opt-in research tooling, outside the admitted runtime inventory.
They use the existing checkpoint codec and actual production row normalizer. They
do not restore a frontend, admit declarations, create source authority or change
runtime Vars. See [measured findings](../RESTORED_IR_SHARING_2026-10-24.md).

From the Ansatz repository root, sample a local uncompressed checkpoint. The
default parent hash is the archived finalizer used for this experiment; supplying
another hash identifies different input, not an accepted consumer.

```sh
python3 experiments/lean-ir/research/profiling/sample-checkpoint.py CHECKPOINT.frames target/profile-sample --functions 4096 --heap 16 --globals 16 --declarations 8 --seed 20261025
mkdir -p target/object-meter/classes
javac -J-Xmx128m -d target/object-meter/classes experiments/lean-ir/research/profiling/ObjectMeter.java
printf 'Manifest-Version: 1.0\nPremain-Class: prototype.profile.ObjectMeter\n\n' > target/object-meter/manifest.mf
jar --create --file target/object-meter/meter.jar --manifest target/object-meter/manifest.mf -C target/object-meter/classes .
```

Set `profile_classpath` to your existing compiled Ansatz/Lean experiment classpath
(including experiment `src`, `test` and the Clojure/data.json jars). This does not
rebuild or select a closed consumer. Start one bounded JVM; add JFR options when
allocation sampling is useful.

```sh
java -Xmx384m -Xss8m -javaagent:target/object-meter/meter.jar --add-opens=java.base/java.lang=ALL-UNNAMED --add-opens=java.base/java.util=ALL-UNNAMED --add-opens=java.base/java.math=ALL-UNNAMED --add-opens=java.base/java.util.concurrent.atomic=ALL-UNNAMED -cp "target/object-meter/meter.jar:$profile_classpath" clojure.main
```

In the REPL:

```clojure
(load-file "experiments/lean-ir/research/profiling/measure-rows.clj")
(def result (profile-restored-ir/compare! "target/profile-sample/function-uniform.frames" 4096))
(profile-restored-ir/save! "target/profile-sample/result.json" result)
(into {} (for [[label graph] (:sizes result)] [label (select-keys graph ["bytes" "objects"])]))
```

The Java agent provides exact VM shallow sizes. Its graph walk deduplicates object
identity, excludes static fields, and stops at Class/ClassLoader/Thread/Reference
boundaries (reported explicitly). It fails on inaccessible fields or the two
million object limit. This is a strong reachable graph sum, not a heap dominator
analysis, global JVM memory or a proof of full-frontend fit. It does not force GC.

Uniform reservoirs and the eight largest frames per kind are separate files. Do
not mix them into a supposedly representative mean. Full input bytes are hashed
before publishing a sample; selected frame bytes are verified again on extraction.
No sample is restoration/admission authority.

For allocation sampling, add
`-XX:StartFlightRecording=filename=target/profile-sample/profile.jfr,settings=profile,maxsize=32m,dumponexit=true`
to the JVM command. In this isolated JVM, the optional
[jfr-allocations.clj](jfr-allocations.clj) helper dumps the first recording and
streams allocation samples into class/stack summaries:

```clojure
(load-file "experiments/lean-ir/research/profiling/jfr-allocations.clj")
(object-profile.jfr/snapshot! "target/profile-sample")
```

Weights are sampled allocation estimates for everything in that recording,
including measurement code. Use separate recordings for distinct workloads;
do not interpret them as retained heap or exact allocation totals.
