# UInt64 narrowing reference

The two original declaration rows are authenticated against the accepted Lean
4.33.1 CAS index. `provenance.json` pins their fixture and upstream source files.

`NarrowOracle.c` copies the exact pinned `lean_uint64_to_uint32` inline body.
Its eight native results cover both lane boundaries, high-bit words and the
maximum UInt64. This is a C cast reference, not a Lean frontend or whole-program
execution result. Regenerate with any C11 compiler, for example:

```sh
cc -std=c11 -O2 NarrowOracle.c -o /tmp/ansatz-narrow-oracle
/tmp/ansatz-narrow-oracle > native-vectors.json
```

Update hashes intentionally when regenerating. Normal JVM tests consume the
recorded vectors and require no native compiler.
