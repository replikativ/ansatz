# Java-first Ansatz APIs

Research review, 2026-10-28. These recommendations are not a shipped API promise.

Java applications can use Ansatz without writing Clojure. Clojure remains a
transitive runtime dependency of the present implementation, including the kernel
Env's persistent collections and the storage bridge. A dependency-light Java-only
kernel would be a separate extraction, not a requirement for Java source usage.

The [Clojars core page](https://clojars.org/org.replikativ/ansatz) lists Maven and
Gradle usage; the reviewed release was `org.replikativ:ansatz:0.2.413`. Consumers
configure `https://repo.clojars.org` alongside Maven Central. Core `build.clj`
emits the POM. The optional Lean module declares `org.replikativ/ansatz-lean`, but
its public publication was not verified; a source build coordinate is not release
availability. Follow the official [Maven repository guide](https://maven.apache.org/guides/mini/guide-multiple-repositories.html)
or [Gradle repository guide](https://docs.gradle.org/current/userguide/declaring_repositories_basics.html).

## Existing entry points

`modules/lean/src-java/ansatz/lean/LeanRuntime.java` already provides Java DTOs,
provider/extern SAMs, source loading, explicit initialization, typed calls, forks
and AutoCloseable contexts. It uses the supported
[Clojure Java embedding API](https://clojure.org/reference/java_interop#_calling_clojure_from_java).
Its prepared provider still requires opaque Clojure candidate/configuration
objects. Context close releases resident roots; it never closes the borrowed
provider source lease. A Java bootstrap producer remains missing.

Direct advanced kernel entry points exist in `src-java/ansatz/kernel`:
`TypeChecker.inferType`, `check`, `isDefEq`, `checkConstant`, mutual and inductive
checking; `Env` supports persistent overlays, lookup and external lazy resolution.
Public Java visibility does not make all those classes a stable SDK. Checkers
are mutable; `ConstantInfo` exposes mutable metadata/value/arrays; Expr payloads
include exposed arrays. `Env.addConstant` performs insertion, not checked admission.

## Recommended stable boundary

Add a narrow facade with owned store leases, pinned environment views, immutable
declaration views/builders, explicit checking budgets and checked admission that
returns a persistent child. Keep raw kernel access as an explicitly advanced
interface, with source/generation and thread-confinement rules. Do not return
unscoped IFn-backed resolvers or mutable checker state through the stable facade.

A possible usage shape, not existing code:

```java
try (StoreLease store = AnsatzStores.openExisting(path, options);
     KernelContext kernel = AnsatzKernel.open(store.snapshot("mathlib"), policy)) {
    DeclarationView theorem = kernel.lookup(NamePath.parse("Nat.add_comm"));
    CheckResult result = kernel.check(proof, expectedType, budget);
    try (KernelContext child = kernel.admit(declaration, budget)) {
        // The child carries the checked addition.
    }
}
```

Context/handle generations and borrowed backing leases must remain explicit.
Retained failures can also depend on the source lease. Thread-confine checkers
and store resolvers first: storage `branch-resolver` has non-thread-safe Name/level
caches despite Env's concurrent shared declaration cache. A per-context mutex
does not make a shared resolver safe across independent contexts.

## Mathlib loading

Adapt `ansatz.export.storage/load-env` and its lazy external resolution, rather
than eagerly reconstructing the store. Require explicit branch/version/value
policy. `ansatz.store/compatibility-errors` checks format/cohort/capabilities; that
does not independently verify declarations or authenticate a source.

`ansatz.core/init!*` loads `:defs-only` and omits most theorem bodies. Independent
reverification of arbitrary theorems requires a full-value policy. Storage
`open-store` may create a blobs directory, and `close-store` flushes writes;
an owned read-only StoreLease needs implementation, not merely renaming these
operations. Avoid the global proving environment and `init!` as the Java isolation
model. `session/with-session` serializes/restores global state but cannot undo
external effects.

## Campaign placement

Finish genuine Java provider consumption with the existing Lean facade first:
jars-only `javac` consumer, exact BigInteger/Unicode, load/call/fork/close, retained
versions/failures and cross-context rejection. The module already has isolated
consumer tooling and genuine-provider historical evidence; the new runtime tier
needs its own current-head acceptance.

Then scope a stable kernel/store facade separately, including real read-only
opening, resolver concurrency, declaration provenance and release coordinates.
Do not make that larger SDK a prerequisite for this Lean runtime campaign. Keep
the two Java execution drivers behind the runtime's public behavioral contract;
one shared value/heap/extern implementation should serve forkable explicit
execution and mutable closed execution.
