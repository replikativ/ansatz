# Foreign imports and synchronous IO

[Bindings.lean](Bindings.lean) declares bodyless pure imports for Unicode length,
a custom record and a nullary value, plus an IO import for configuration reads.
Each uses a standard `ansatz_jvm_` extern marker. It also supplies a noinline IO
reference definition that runs without a host replacement.

[Main.lean](Main.lean) calls those declarations and catches Lean IO errors. The
[application-JAR consumer](../../consumer/ForeignFFISmoke.java) supplies Java and
Clojure implementations, constructs the record from its admitted result type,
and exercises explicit `LeanIOError` values, missing bindings, wrong effects,
unexpected failure, cancellation and reference replacement.

Bodyless imports require every selected implementation before initialization;
their opaque placeholders are not executable fallbacks. Native execution needs
actual native implementations, so the pure-reference corpus's native oracle does
not establish native equivalence for these imports. Pure implementations remain
responsible for the declared purity contract.

Prepared test artifacts belong under `consumer/resources/lean`, outside the SDK
runtime JAR. See the [binding guide](../../FFI.md) for API usage and limits.
The candidate producer is locally built; publication and release remain pending.
