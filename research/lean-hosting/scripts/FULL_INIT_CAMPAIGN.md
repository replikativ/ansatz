# Full Init REPL campaign

This is an experiment over the authenticated, ignored artifacts listed in
`full-init-assembly-probe.clj` and `typed-witness-next.clj`. It is not a public
bootstrap API or a shipped ordinary-file compatibility claim. Compile the parent
Java sources first if they changed. Run from `experiments/lean-ir`.

Use an external process guard with an explicit heap, RSS, system-memory floor
and lifecycle budget. A 2 GiB diagnostic completed 793 real callbacks but did not
finish finalization. A longer run must budget preparation, guest finalization,
strict checking, and subsequent file experiments separately. Guest fuel does not
bound Java checking, compilation, IO, or elapsed time.

Load definitions and start one worker, leaving the REPL available for bounded
inspection. The output prefix must be new; its JSONL file is created exclusively.

```clojure
(binding [*ns* *ns*] (load-file "scripts/full-init-campaign.clj"))

(def boot-job
  (future
    (let [prepared (prototype.full-init-campaign/prepare!
                     "../../target/artifact-contract/full-init-next/headless-1")]
      (if (= :prepared (:phase prepared))
        (prototype.full-init-campaign/finalize!)
        prepared))))

(prototype.full-init-campaign/summary)
```

Use printer-local limits when starting the REPL; do not change global
`*print-length*` or `*print-level*` while guest code or fingerprinting runs.
The runner prints/returns scalar summaries and writes scalar JSONL observations.
`checkpoint` deliberately returns large borrowed diagnostic packets: never print
or generically serialize that return value.

`finalize!` uses the existing mutable backend without the experimental reference
prefix. It stops at `:finalized` only after actual guest IO success; this state is
still unchecked. `:guest-io-error` retains its actual owned error IO result.
`:failed` retains the terminal cause and named owner/checkpoint alternatives.
No phase retries a started callback, finalizer, or strict-check operation.

The subsequent default 3 GiB run stopped on callback 1,123: the shared-name
witness exhausted its 20M helper budget on a generated UInt macro. See the
[terminal observation](../measurements/full-init-default-fuel-failure.json).
Increasing the process lifecycle alone does not address this failure.

The additive shared-name/linear-collector candidate is selected explicitly. Build
and validate it with `scripts/build-witness-shared-names-linear-oracle.sh` first;
the build preserves the adopted artifacts and checks every old declaration.
Then pass the authenticated artifact and digest as the second `prepare!` argument:

```clojure
{:shared-linear
 {:artifact "target/witness-ir-shared-names-linear/RuntimeCompileShim.source.jsonl"
  :expected-sha256 "4b0d1548a3721ac87fac48a1260c4cd33181ac5baa60498dec25e49825f78ea4"}}
```

This option runs the additive stage before final closure completion and capture
of the new typed witness capability. Existing function objects and unrelated
binding objects are preserved. The default helper is unchanged. Option syntax
is rejected before campaign acquisition; artifact-byte authentication occurs in
the selected stage, with assembled owner/source diagnostics retained on failure.
Native witness parity and collector benchmarks do not establish full Init or
ordinary resident acceptance; record the actual selected helper and result.

After `:finalized`, inspect the remaining resource budget and actual heap before
explicitly starting strict checking:

```clojure
(def checking-job (future (prototype.full-init-campaign/strict-check!)))
(prototype.full-init-campaign/summary)
```

Checking consumes the actual IO owner, verifies the entire checked-constant map,
and associates the exact imported guest Environment. The original catalogue,
helper registry, policy and binding objects stay retained from preparation.
No catalogue is reopened and no import is replayed. Successful strict output is
saved before any fallible observation, and a claimable phase is published only
after its logging finishes. Historical checking duration is not a guarantee for
the current run.

The runner holds its source, writer and diagnostic branches for subsequent REPL
work. Prevent concurrent source closure. Do not reload driver/type definitions
while a campaign is active. Discard all borrowed worlds/contexts before closing
the source, or end the scoped process to discard them together. A scalar log is
not a resumable checkpoint. The separate completed-finalizer checkpoint draft
still requires independent review, bounded-allocation hardening, a real binding
factory and actual finalizer→restore→checking→resident-call acceptance.

The reference-prefix callable and smoke helper are separate definitions-only
experiments for canonical prepared worlds. Loading them does not install a
runtime hook. Their measured tiny-helper improvement does not establish general
snapshot admission equivalence or frontend throughput.
