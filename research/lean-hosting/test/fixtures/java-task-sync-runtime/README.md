# Original synchronous Task / Promise fixture

The 60 rows are the exact static dependency closure of the 50 original root and
boxed-wrapper rows selected in `root-names.json`. Every exact typed Name and raw
CAS SHA was checked against the accepted producer index (`74d833d5…`). The JSON
contains original row bodies, ABI/borrow flags, dependencies and runtime metadata;
only top-level `pretty` was removed. Per-record SHA is the original CAS SHA, while
`provenance.json` separately hashes this derived formatted fixture.

The fixture includes metadata for unsupported async operations to preserve the
original source selection. Presence does not imply that Java executes those
operations. The source/runtime authority is Lean commit `819816b2…`, with source
and Apache-2.0 LICENSE pins in the provenance file. This is not a restored image,
producer executable proof, or a frontend success receipt.
