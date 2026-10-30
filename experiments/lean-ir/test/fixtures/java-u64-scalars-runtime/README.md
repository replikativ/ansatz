# Original UInt64 scalar family and arithmetic oracle

`original-rows.json` has thirteen exact extern roots and their thirteen genuine
boxed wrapper bodies. `config-rows.json` has the reached original Config.toKey,
its boxed wrapper and three original enum conversion bodies, serialized compactly.
Each record retains its complete original CAS SHA and typed Name; only optional
pretty text was removed from the normalized fixture. `provenance.json` pins these
fixtures, producer source index, pinned upstream files and oracle artifacts.

`pinned-inline.h` contains verbatim inline bodies from pinned Lean lean.h with
its copyright/author notice; LICENSE is the upstream Apache 2.0 license. Local
`oracle.cpp` supplies only typed input/output scaffolding. Reproduce with:

```sh
python3 run-oracle.py --lean-repository <lean-source-repository> --output <ignored-output-directory>
```

The script verifies exact upstream file/body correspondence before compilation,
bounds compiler/oracle resources and reads the vectors at runtime. It writes
native-vectors.json/native-receipt.json in the requested output directory. The
checked-in vectors came from the recorded compiler and successful bounded run.
No full native runtime, Lean object ABI, JVM memory or frontend scaling result
follows from this arithmetic-only oracle.
