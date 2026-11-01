# Original Expr cache read and constructor closure

`original-rows.json` contains46 original static-closure rows selected from the
accepted source index. `layout-evidence.json` records actual constructor shapes
and scalar stores from all12 original Expr constructor override rows. Original
CAS hashes and typed Names are retained; only optional pretty text is removed.
The provenance pins both fixtures and upstream source files.

`pinned-inline.h` contains verbatim pinned `lean_expr_data` and
`lean_ctor_get_uint64`, with upstream attribution and Apache2 LICENSE. The local
C++ driver supplies modeled storage/API/type scaffolding, not complete Lean
allocation or reference counting. It is explicitly a scalar offset/read oracle.
Reproduce with:

```sh
python3 run-oracle.py --lean-repository <lean-source-repository> --output <ignored-output-directory>
```

The script verifies full upstream header SHA and exact algorithm extraction before
bounded compilation/execution. The original Level.data override remains guest
code, including its special zero case; no native Level accessor is fabricated.
