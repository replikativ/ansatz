# Source lease checks during hosted frontend execution

`source-setup/guard-source!` authenticates the issued composite receipt, exact
SourceBinding and its accepted profile, then checks the open catalogue lease.
It now uses `catalogue/source-token` for that last step. This existing API holds
the catalogue lock and checks its closed flag and current index size, modification
time and file key. Every guard still performs that check. It does not memoize a
live lease or grant code-row authority.

The former anonymous-Name lookup performed the same lease check plus Name
encoding, hashing and binary index reads. Those searches were unrelated to the
guard's result. Actual code lookups retain their bounded raw-byte hash and typed
Name checks. The catalogue's stated protection remains ordinary file replacement
or rewrite detection; it does not protect against a malicious host restoring
timestamps.

In the retained 384 MiB JVM, an instrumented warm arithmetic file load made
30,884 source-guard calls. Their inclusive elapsed time was 8.55 seconds, while
7,854 Java advance calls took 0.50 seconds. Instrumentation increased the total
load time to 16.63 seconds; these overlapping timers must not be summed.

After replacing the lease-only searches, two fresh warm file loads completed in
4.392 and 4.593 seconds, compared with the earlier uninstrumented 10.791 seconds.
The advance quantum stayed at 100 instructions. Child preparation in the first
new run took 2.255 seconds; an earlier preparation took 5.323 seconds. These are
sequential REPL observations on a busy machine, with warmed original code and
OS/JVM caches, not a controlled speedup benchmark or cold-project measurement.

The second run called the checked and linked `hostedStep` with 0, 42,
`Long.MAX_VALUE`, 2^64 and 2^200; every result was the input plus one. Actual EOF
and normal retirement completed, releasing 12 additional owner occurrences and
534 runtime roots. The first new run checked loading and retirement only: a
test-harness map expression evaluated cleanup before its calls, so those calls
were repeated in explicit sequential bindings in the second run.

Focused checks passed 16 tests / 99 assertions, including exact source identity,
repeated live-lease checks, foreign-source rejection, closed catalogue rejection
and actual index replacement detection through `source-token`. No Java engine,
kernel, guest reference-counting or opaque registry changes were required.

The full Java runtime regression passed 160 groups / 1,537 tests / 60,398
assertions with zero failures and errors in a separate 384 MiB validation JVM.
The source review was clear. External log:
`target/java-source-lease-v1/full-gate.log`, SHA256
`4f5073094a282cfca08ee3f1259dacdf964cf7383686d05d2b856699892e213d`.
The second complete file observation is recorded externally in
`target/java-compact-name-runtime-v1/direct-lease-file-validation-v11.edn`, SHA256
`2405acaacc8ecd995e7a2df6c0dc0bc1a7631b85e90556f64d29cd3b9d593ace`.
