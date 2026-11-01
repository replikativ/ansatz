# Borrowed result decoder models

The JSON fixture contains four constructor-layout families copied from the genuine native entry probe identified in the provenance file. It is structural test input, not an artifact receipt, native type proof, or authority to allocate guest values. The `ModelNode` test class is deliberately not an Interpreter Node.

Load the canonical SDK signature, codec, entry, and startup namespaces, including the Java LeanUnit enum, before loading `src/ansatz/lean/jvm/value.clj` and `test/ansatz_lean_jvm_value_checks.clj`. From the module directory run:

```clojure
(ansatz-lean-jvm-value-checks/check!)
```

The one-argument form accepts an explicit fixture path for a retained REPL whose working directory differs. The 14 model families cover immutable nested results, Optional distinctions, iterative list tails, shared DAG copying, cycles, invalid runtime shapes, persistent constructors, missing witnesses, logical field indices, occurrence limits, interruption, and IO envelopes. The changed-index model demonstrates metadata interpretation only; the actual entry validator separately rejects altered cohort facts.

Worker validation is reader-only: 17 source forms and 29 model forms read successfully. No JVM or native execution was launched by the author. Actual runtime results require the parent-operated interpreter gate, separately from these models.

The decoder borrows every guest value. It neither allocates guest objects nor changes guest reference counts. Its caller retains the single actual result-root occurrence until complete decoding, then releases that root using its existing ownership journal. IO errors return only an error classification; no guest error alias escapes. Legacy IO Unit keeps its existing independently authenticated decoder and does not obtain a guessed v2 layout here.
