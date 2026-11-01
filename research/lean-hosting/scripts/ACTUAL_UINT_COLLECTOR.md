# Actual UInt collector canary

This experiment runs two genuine Lean collector functions on the same native-selected
`IR.FnBody`. It isolates the generated UInt macro that exhausted the original
collector's 20M-step budget during the full-Init campaign. It does not restore or
finalize a guest Init Environment, invoke evalConst, or establish ordinary-file
acceptance.

Run commands from `experiments/lean-ir`. Build the pinned exporter, generic IR
value transport, and shared-name/linear witness first, following their existing
[exporter](build-exporter.sh), [IR transport](../research/WITNESS_IR_VALUE.md),
and [linear witness](build-witness-shared-names-linear-oracle.sh) instructions. The canary needs
`target/witness-ir-value/libIRValueTransport.so`,
`target/witness-ir-shared-names-linear/RuntimeCompileShim.{olean,source.jsonl}`,
the adjacent helper shared library, the authenticated declaration store under
`target/parser-module-store`, and `target/lean-export-aliases.jsonl`.

Build a fresh native canary under an external RSS/deadline guard:

```bash
ANSATZ_UINT_CANARY_OUTPUT=target/actual-uint-body-canary-new \
  scripts/build-uint-collector-body-canary.sh
```

The script refuses an existing output path. Its relative paths resolve from the
experiment directory even when invoked elsewhere. It pins Lean 4.33.1's exact
commit, bounds the native stack to 64 MiB, records producer-input hashes, exports
three typed root arrays, and runs the existing independent transport checker to
publish their descriptors. Rebuilding requires reviewing and explicitly supplying
the new descriptor pins; output-path changes may change descriptor bytes. Neither
local hashes nor the transport checker attest an arbitrary producer's honesty.

The following explicit options describe the accepted V3 artifacts. The files are
local experiment outputs, not included in the repository. No loader discovers or
silently substitutes newer artifacts. The declaration-index digest is separately
pinned by the probe to
`74d833d577923821b982e8a9e872a38b5cad011513eb18870b51417e13397f0e`.

```clojure
(def options
  {:store-root "target/parser-module-store"
   :shim {:path "target/witness-ir-shared-names-linear/RuntimeCompileShim.source.jsonl"
          :sha256 "4b0d1548a3721ac87fac48a1260c4cd33181ac5baa60498dec25e49825f78ea4"}
   :aliases {:path "target/lean-export-aliases.jsonl"
             :sha256 "51b80c4da0634b7f9d11496923865d6e9c171e29b0d5e0cc738480ba18d01e84"}
   :descriptors
   {:body {:descriptor "target/actual-uint-body-canary-v3/uint-macro.body.verified.json"
           :descriptor-sha256 "24ba316176fa0c28ecfb00acd69910b33f47b7af6d90edd4d3bcee3e5724deae"
           :source "target/actual-uint-body-canary-v3/uint-macro.body.jsonl"}
    :decl {:descriptor "target/actual-uint-body-canary-v3/uint-macro.decl.verified.json"
           :descriptor-sha256 "4fe177aa9cf12b6db0e9da24b2f376971eedf95d1071ac3679baf6a378e9f002"
           :source "target/actual-uint-body-canary-v3/uint-macro.decl.jsonl"}
    :expected {:descriptor "target/actual-uint-body-canary-v3/uint-macro.expected.verified.json"
               :descriptor-sha256 "a2e32ca0d4a8c637ad54b576d3c80b02210e7fbfaa65479f4c5d209133a76832"
               :source "target/actual-uint-body-canary-v3/uint-macro.expected.jsonl"}}}
)
```

In a separately guarded REPL (`clj -J-Xmx<size> -M`, with an explicit heap
chosen for the available memory), load definitions and explicitly run the probe. Budget at least the recorded process envelope below, including
preparation and cleanup. Guest instruction fuel does not bound wall time, native
IO, or host compilation. Printer limits should be local to diagnostic printing.

```clojure
(binding [*ns* *ns*] (load-file "scripts/actual-uint-collector-probe.clj"))
(def runner (prototype.actual-uint-collector-probe/prepare! options))
(prototype.actual-uint-collector-probe/summary runner)
(try
  (prototype.actual-uint-collector-probe/run!
    runner {:backend :mutable :observe! prn})
  (finally (prototype.actual-uint-collector-probe/close! runner)))
(prototype.actual-uint-collector-probe/summary runner)
```

`prepare!` authenticates the exact parsed index stream and caller-pinned helper,
alias and descriptor bytes. It opens three Stores at disjoint native ID bases and
checks their actual returned identities. Stack-safe projection/equality checks the
native Decl, its native JSON, the saved catalogue's exact IR row, and the selected
body. Provenance requires imported FDECL selection from Init classic+meta/private,
no missing constants, no sorry, and successful native compacted roundtrips. The
primary root is `Array IR.FnBody`; the other arrays are explicitly Decl/Json,
not ModuleData or serialized Environment values.

Both guest runs use the same read-only body, source leases and linked actual
wrapper functions, with independent worlds/sessions and a 20M-step budget. The
original outer fuel pause is recorded and abandoned, never resumed. Completed
results must equal the exact native ordered Name array, including duplicates;
their result owners are released once in their own branch. Handles reject a second
run. A failure is terminal: retain diagnostics, close resources, and terminate the
owned process instead of retrying the failed computation. `checkpoint` returns a
borrowed diagnostic graph; do not print, serialize, or resume it. `close!` rejects
concurrent execution and drops worlds/catalogue before closing source leases.

The accepted native V3 producer took 6.02 seconds with 935,100,416-byte peak RSS.
The accepted mutable guest process took 108.21 seconds with 1,018,900,480-byte peak
RSS, exited 0, and closed all three Stores. The original collector exhausted
20,000,000 instructions with 76 paused frames. The linear collector completed in
154,177 instructions / 699.35 ms and matched all 1,522 native dependencies in
order. This proves the isolated linear/native match and reproduces the old fuel
failure; it does not establish old/new guest equality because the old run paused.
Only the mutable backend was measured in this acceptance run.

That historical guest run loaded the reviewed streaming-index API from a separate
classpath source copy. The now-integrated `prototype/declaration_store.clj` is
byte-identical: SHA256
`d9f24ac2e41d737cec01e88e25c65d3aab955f738d25da705dec456307723150`.
The tracked Lean source and C++ adapter are byte-identical to the accepted V3
inputs (SHA256 `eea7fc4a98b7c390c36506e3ee18f9ed1ecf111ccb9c6a46f3e644cf1f579c8c`
and `f9b7c33aac79c67d4f7586d53ac22d2e274e5d855b33e8c034e85520df6114e3`).
Integration changes the build script's source paths/cwd handling and the runner's
namespace/documentation only. The tracked native build subsequently passed in
6.02 seconds with 933,859,328-byte peak RSS. The tracked probe definitions load
in the integrated runtime suite (772 tests / 66,212 assertions); no second guest
collector timing is inferred from these integration checks.
