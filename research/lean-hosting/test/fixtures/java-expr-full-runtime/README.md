# Private complete two-pass Expr fixture

The twelve-line safe `Oracle.lean` calls the original pinned Lean 4.33.1 native through low-level MetavarContext APIs, with output plus complete known expression-assignment-key/domain readback. Root reported exact expected output, exit 0 and empty stderr; see `native-receipt.json`. This is `--run`, not AOT or a native heap/ownership trace.

The private Java job reuses the [nineteen-role original fixture](../java-expr-direct-runtime/README.md) and its execution closure, pinned by `provenance.json`; no duplicated source issuer or new initialized-state fact is inferred. Java tests use original map/getter/setter/constructor IR with an explicitly labeled delayed-map storage setup adapter. Stale-cache and malformed-body cases are backend models.

At this private checkpoint native 530 remained unregistered; the later configured native API is documented separately. Private 21 tests / 111 assertions passed in the parent's retained JVM; native activation and full combined integration require separate gates. The author ran only bounded javac/jar, no interpreter JVM or native tool.
