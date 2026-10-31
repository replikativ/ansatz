# Pinned Expr abstraction fixtures

Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
`original-rows.json` contains exact raw/boxed abstractRange and abstract declarations
plus the nine existing original constructor roles. Optional pretty text is omitted;
each row SHA identifies the complete original CAS record. `provenance.json` pins
fixture bytes, source files, accepted index and the 55-row/no-initializer metadata
closure. See [runtime contract](../../../research/JAVA_EXPR_ABSTRACT_RUNTIME.md).

`Oracle.lean` and `expected-native-output.txt` describe eleven original-source
content/identity observations. `native-receipt.json` records the exact pinned
binary, input/output hashes and successful `--run` result. This is not an AOT,
allocation or RC trace comparison. Small heap Nat, malformed carrier/storage and
Host/constructor substitutions in the Clojure suite are explicitly backend models.
