# Native v3 regression captures

These files preserve genuine Lean 4.33.1 native observations for offline JVM and
Clojure regression checks. They do not issue compiler receipts, authorize a
producer, establish live byte custody, or admit an entry. No native executable,
compiled module, sysroot blob, or installed library is included.

| File | Purpose |
| --- | --- |
| `entry-evidence.json` | Original selected-entry v3 evidence. |
| `oracle-entry-evidence.json` | Broader datatype oracle entry evidence. |
| `typed-export.jsonl` | Exact final typed-source exporter stream for the oracle. |
| `producer-build-receipt.json` | Exact independently pinned standalone producer build receipt. |
| `builtin-observations.json` | Compiler-only builtin witness observations. |
| `oracle-type-observations.json` | Compiler-only datatype witnesses, including `Option Unit`. |

`provenance.json` records SHA-256 and byte counts for every copied file, exact
original capture locations, the three maintained producer source hashes, and the
reviewed entry executable and source-closure identities. Capture locations are
historical records; tests need only this directory and tracked producer sources.
Process receipts retain their original command, environment, and historical
paths unchanged. They describe those runs and must never be executed as scripts.

`receipts/` retains the actual native process receipts. The two probe stdout
files include the original `NOMINAL_WITNESS_OBSERVATIONS_JSON` line and success
marker. Their corresponding observation JSON files are exactly the JSON value
on that marked line. Entry evidence and the typed exporter stream are exact
stdout copies; their bytes and hashes match their process receipts. No evidence
JSON value has been rewritten. `inputs/` retains entry requests, advisory origin
inventories, and pathless product manifests supplied to the captures.

`sources/` contains the exact small fixture and probe sources used by these runs.
In particular its `NativeNominalFixtures.lean` has SHA-256
`395e9c3f355631f1b4a22594ad9af849957914cc148f2ceed2828c8ca8f5a860`;
it differs from the older source in `../nominal-observations/sources/`.
The maintained producer implementation is referenced by hash rather than copied.

## Regeneration

Regeneration requires the pinned Lean commit recorded in `provenance.json`, the
recorded maintained producer sources, and the exact fixture sources here. Work
in a fresh repository-local temporary directory; keep native jobs serialized
under the monitored compiler transport and its resource bounds. Building the
standalone helper also requires the explicit memory checks and reviewed link
configuration in `tools/lean-producer/build-entry-v3.py`.

1. Compile the fixture modules and the independent `NativeDatatypeOracle` module.
   Capture the typed-source exporter stream separately, preserving its complete
   JSONL framing and process receipt.
2. Use the standalone helper's `--entry-origins` command with each retained origin
   request. Capture and recheck every required module's actual product roles,
   including absent sidecars; advisory names alone supply no byte authority.
3. Supply the resulting module-product manifest and matching digest in the entry
   request to `--entries REQUEST --module-products PRODUCTS`. Preserve exact
   stdout, request, manifest, and monitored process receipt for each entry set.
4. For each compiler-only probe, run its `inventory` mode first. Capture and
   recheck actual products, then run with `NOMINAL_WITNESS_MODE=observe` and
   `NOMINAL_WITNESS_PRODUCTS` pointing to that manifest. Extract only the JSON
   after the exact observation marker; retain the raw stdout and process receipt.
5. Audit all hashes, role records, producer cohort identities, and extraction
   equality before replacing fixtures. A different product hash is a new capture
   requiring review, not a reason to edit old evidence to fit a new binary.

The exact command arguments and resource observations for these original runs
remain in their receipts. New captures may have different legitimate product
hashes; they must establish their own compilation and before/after custody.
