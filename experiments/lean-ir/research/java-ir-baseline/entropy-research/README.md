# Original Random initializer research gate

This package preserves the bounded, prior-native-capture gate for the original
Lean `IO.stdGenRef` initializer. It is research evidence, not a public artifact
issuer, complete Init startup implementation, Java kernel certificate, or SDK
Project API. The source boundary is Lean commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (4.33.1).

The 63 original rows are retained byte for byte in `captures/prior-cas`.
`random-gate.clj` authenticates their fixed manifest, stream, individual row
hashes and typed Names, reserves all canonical Headers, and materializes their
bodies. Original dependency vectors remain unchanged. The materializer borrows
the distinct external FAP/PAP targets from each actual body, excluding self;
initializer metadata edges are closure obligations, not body-call Header borrows.

The actual gate executes the genuine raw owned-void initializer and publishes its
`tobject` global result through the initializer protocol. The captured boxed
initializer candidate is not described as an observed native interpreter
selection. The separate fixed `IO.userError` raw row is a codec layout witness;
its digest does not replace authentication of current producer rows. Current
rows may carry different provenance metadata and truthful different digests.

`capture-cas.py` can recreate this exact capture from the previously authenticated
catalogue, CAS, metadata and census, supplied explicitly as paths. It hashes the
catalogue data incrementally, authenticates each raw row and caps the union at
16 MiB. It performs no Lean or JVM execution. `verify.py` checks the portable
package inventory and row pins without either runtime.

For a retained research REPL with `java-ir-baseline`, generation/fork checks and
the matching runtime already loaded, load `random-gate.clj`,
`direct-header-models.clj`, `run-original-random.clj`, and
`run-original-random-error.clj` once. The runners require a prepublished journal
whose `:prepared` value is returned by `random-gate/prepare` and whose status is
`:prepared`. They retain failure custody; they do not claim arbitrary unwind.
The deterministic runner is `run-original-random-v2!`; its seed argument records
the expected source pattern (capability configuration is explicit in the prepared
value). The error runner is `run-original-random-error-v1!`.

Historical receipts retain the actual source cohort and distinguish deterministic,
all-FF unsigned, default JDK DRBG, expected provider error, and official native
oracle observations. Read `validation.json` before treating any result as evidence
for a later source cohort. Native oracle data is not a Java typechecking claim.

The portable JDK entropy profile is deliberately distinct from POSIX entropy.
Its configured SecureRandom service is shared by healthy idle forks; existing
guest generator state is copied, no reseeding occurs, and statistical independence
is not asserted. Cooperative execution budgets do not impose a hard deadline on
a provider callback. No worker JVM or native process was launched to package
these records.
