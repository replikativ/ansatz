# Exact original scalar widening to UInt64

The six fixture records are three original extern rows and their three genuine
boxed wrappers. Full typed Names and original CAS SHA256 identities are retained;
only optional pretty text was removed. `provenance.json` pins the fixture,
producer index, upstream header and compiled arithmetic oracle artifacts.

`pinned-inline.h` copies the three cast bodies verbatim from pinned Lean lean.h,
with its author/copyright notice and Apache2 LICENSE. `oracle.cpp` only supplies
fixed64-bit/type-domain assertions and runtime input/output. Reproduce with:

```sh
python3 run-oracle.py --lean-repository <lean-source-repository> --output <ignored-output-directory>
```

The script authenticates the upstream header and exact body extraction before
bounded compilation/execution. It does not execute a Lean module, Init, an image
or JVM. UInt16 input execution remains unsupported.
