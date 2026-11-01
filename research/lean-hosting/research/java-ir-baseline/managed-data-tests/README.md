# Managed argument construction checks

`ManagedDataChecks.java` is a standalone check against the actual Interpreter class. It creates guest values only through `constructDataArguments`; reflective access inspects custody and injects refused lifecycle states for models. It supplies no native constructor/type authority.

Root operator sequence, using the reviewed runtime classes directory:

```sh
javac --release 11 -cp RUNTIME_CLASSES -d CHECK_CLASSES managed-data-tests/ManagedDataChecks.java
java -Xmx192m -cp RUNTIME_CLASSES:CHECK_CLASSES ManagedDataChecks
```

The author performed source and whitespace review only; no JVM/native process was launched. Root owns compilation and execution.

The checks exercise immutable leaf admission (including Unicode/NUL and large integers), snapshots independent of caller arrays, nested ownership, actual explicit release, invalid references/aliases/orphans, existing Node rejection without RC changes, extensible BigInteger rejection before overridden methods, malformed UTF-16, per-leaf/aggregate budgets, allocation-counter overflow, lifecycle refusal, and a long proper list released through the real explicit release driver.

The internal API is a mechanical scalar-free constructor builder, not a type validator. The trusted SDK codec must derive each recipe from authenticated compiler layouts and a validated Lean signature. Empty constructors are Long tag immediates. Every fresh node must occur once, either in an earlier-reference parent edge or in the returned roots; shared host subtrees must be copied into separate recipes. Existing guest values, scalar payloads, arrays, resources, and closures are refused.

Bounds are 100,000 field/root occurrences, 4,194,304 aggregate integer bits (Long occurrences conservatively charge 64), and 1,048,576 aggregate UTF-16 units. Individual BigInteger magnitudes are at most 4096 bits and String leaves at most 65,536 UTF-16 units. These are transport bounds, not arithmetic semantics.

Keep construction, argument-root journaling, start and drive within one Project lease. Before start the caller owns the returned root occurrences. A successful owned boxed call adopts them; clear the host aliases without DEC. An uncertain start failure retains the journal and follows the certified whole-branch abandonment protocol. Dropping unpublished fresh Java heap after allocation failure does not claim guest RC unwinding.

Scalar and special-data support must use explicit future recipe variants with separately reviewed carriers, layouts and ownership; this API never interprets tags as Array/ByteArray/Ref/task kind metadata.
