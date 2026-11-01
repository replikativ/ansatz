# Direct guest Json interpreter witness

Stage 1 appends `RuntimeCompileShim.exportEvalConstWitnessValue` after the
existing helpers and main in `lean/RuntimeCompileShim.lean`. It returns owned
`IO Json` instead of printing `IO String`. The interpreter-declaration lookup,
boxed selection, complete dependency walk, source module attribution, schema,
producer string, pinned commit, profile and sorry-dependency evidence are the
same as the original `exportEvalConstWitness`. This adds no cache or authority.

The new entry has the same argument ownership as the original entry, inferred
by the pinned compiler; link its actual producer IR and boxed wrapper rather
than inventing a signature. The host must borrow/decode the actual IO payload,
run the same structural witness/provenance/IR/ABI checks, then release the owned
IO result normally. Do not treat successful decoding as permission to execute
code. The old string helper remains available and unchanged.

The producer artifact `target/runtime-compile-shim-json-value-source.jsonl` has
464 rows, nine new declarations and zero initialization actions, SHA256
`45dcd510324bdff6d0d95ac1093d26a087ad1d6e513e7fec1ea2d07f6a8873fd`.
Comparison against the 455-row source-module witness artifact with SHA256
`632aef00b22b4144aa78cc54e3e3e34533fdd3bab72f3cea8177f647933100db`
found no changed or removed existing rows; the manifest is identical. The
complete inventory is `target/runtime-compile-shim-json-value.diff.json`.
No old closed constant or helper requires replacement or initialization.

## Native evidence

`lean/GuestJsonWitnessOracle.lean` uses real native frontend compilation and
owned source-module finalization as an oracle. It compares the old helper's
string with the new helper's `Json.compress` exactly for local, absent, imported
and mixed local/imported static closures. All four comparisons passed.

It also exports an actual compacted object DAG containing 18 Json roots: all six
constructors, negative small Int, positive/negative MPZ, exact decimal forms,
Unicode/NUL/escaping, empty objects/arrays, shared nested objects and the four
actual witnesses. The 285-node graph passed native reconstruction comparison
and records 170 sharing revisits. It contains no Environment or native execution
objects. Compaction establishes actual mapped constructor scalar extents before
export; `native/GuestJsonTransport.cpp` reuses the existing strict generic DAG
producer rather than reading uninitialized native heap padding.

The physical oracle confirms Json.bool's source one-byte scalar field occupies
an eight-byte padded compacted tail; JsonNumber is constructor 0 with two object
fields (Int mantissa and Nat exponent); TreeMap inner nodes have five fields.
The decoder must handle these actual layouts, raw immediate Int words and signed
MPZ contextually. The decimal is mantissa times ten to the negative exponent;
printing and decoding must not silently convert it through floating point.

Reproduce serially from this experiment directory with
`scripts/build-witness-json-oracle.sh` after building the pinned exporter. It
emits `target/witness-json-value/guest-json.jsonl`, its native compressed expected
value, and the helper artifact. The native log is
`target/witness-json-value/oracle.log`; the small tracked result is
`measurements/hosted-witness-json-value.json`. The decoder regression fixture may
be copied from that verified graph. Native oracle work is preparation evidence,
not a claim that a hosted Init import has completed this path.

The host decoder now passes all 18 native roots and four actual witness objects.
Transport and frontend tests also cover unchanged IR/ABI rejection and preserving
the exact owned witness IO result on errors. The actual hosted helper returned
the same complete witness as the current string helper for a freshly compiled
identity: [hosted observation](../measurements/hosted-json-witness-canary.json).
The restored bootstrap used an older string helper without `sourceModule`;
parity preparation refreshes only its five known ordinary helper declarations,
preserving every admitted user function and all closed globals.

The recovered full Init import is running with `:witness-format :guest-json`.
Both transports use the same complete witness validator, exact catalogue IR,
boxed ABI, executable-closure identities and source-import authorization. Guest
JSON projection borrows the tree while its IO wrapper is owned; success releases
the wrapper, while failures expose its owner and matching checkpoint explicitly.
There is no fallback from malformed JSON to catalogue lookup.
