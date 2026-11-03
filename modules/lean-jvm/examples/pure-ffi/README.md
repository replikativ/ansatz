# Pure host implementations with Lean reference code

[Bindings.lean](Bindings.lean) defines a record and seven ordinary noinline pure
functions. [Main.lean](Main.lean) uses them during initialization, through direct
calls, a constant call, List.map, and String.any. [Oracle.lean](Oracle.lean) runs the Lean implementations
without JVM bindings. Its captured output is:

```text
7
46
43,true
10,true
9,true
12
18
[1, 2, 3]
true
false
```

The [application-JAR consumer](../../consumer/PureFFISmoke.java) loads one prepared
artifact twice: first using the reference bodies, then with Java implementations.
It checks the same results and observes every selected implementation, including
the nullary constant and native String.any predicate. It also tests Clojure record
views, a result-constructor factory, unsupported registrations, error/cancellation
propagation and failed-Project retirement.

The prepared artifact is test evidence under `consumer/resources/lean`, not an
automatic SDK runtime resource. The source/oracle snapshots and producer receipt
are recorded in [fixture provenance](../../test/fixtures/pure-ffi/provenance.json).
No native toolchain is used by the application-JAR test. See the
[FFI guide](../../FFI.md) for candidate API usage and limits; v4 producer publication
and release are pending.
