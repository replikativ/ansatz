# Bounded classic header discovery

`prototype.resident-init-prefix/discover-classic-source-header` is an experimental descriptive operation for a caller that already owns a coherent prepared packet and its independently captured resident configuration. It invokes the fixed `RuntimeCompileShim.inspectFileHeader` target after checking its executable closure. It returns the helper's actual updated World/session, the captured text/file name, a bounded header, a status, and scalar work accounting.

The operation does not import, compile, publish, adopt a Context, or issue a graph capability. It does not read paths or resolve packages. General Project loading and native-only reset are separate work.

```clojure
(discover-classic-source-header
  packet
  {:text captured-text :file-name captured-file-name}
  {:configuration configuration
   :limits {:max-source-bytes 1048576
            :max-file-name-bytes 4096
            :max-output-bytes 1048576
            :max-json-depth 128
            :max-imports 1026
            :max-diagnostics 256
            :max-name-nodes 64
            :max-name-bytes 4096
            :max-total-name-bytes 1048576}
   :budgets {:helper-fuel helper-fuel :attempt-fuel attempt-fuel}})
```

These numbers illustrate the API shape; they are not measured defaults or a guarantee that a particular frontend fits. Limits and budgets are required explicitly. The ordinary classic subset requires implicit Init/meta Init followed by ordinary imports. Prelude files, module-system files, and other import flag combinations are outside this slice, although they may be valid Lean source.

A valid parser-error envelope returns `:status :header-error`, diagnostics, and an empty `:requestedImports`. Its updated packet must still be kept: parsing can allocate or affect guest globals and host state. Malformed, oversized, unsupported, or incorrectly attributed envelopes throw with the exact owned result/checkpoint evidence. No automatic cleanup, retry, or Source close occurs.

The caller should fork one scratch branch, capture each file's text once, thread `:packet` through adaptive header discovery, and adopt once after discovery succeeds. Compilation must use the same captured text, rather than rereading a path after inspecting its header. An updated packet or descriptive header is not a checking certificate or import receipt.

The per-operation aggregate reservation covers one fixed helper call and its nested guest calls. It does not cover a whole Project attempt or later compilation. A Project caller must reserve its remaining aggregate before each operation and charge known work or retain an unknown reservation on failure. Success restores only the incoming session's `:fuel` policy, preserving the actual child session's registries and caches. This keeps a small discovery limit from silently becoming the later compilation policy.

The shared header validator bounds UTF-8 input/output bytes, lexical JSON depth before parsing, import and diagnostic counts, structured module Name spines and per-name/aggregate bytes, and the byte offset against the exact captured source. Graph publication/import reuse the validator and additionally require a successful header whose ordered imports exactly match their issued parent/root selection. The legacy frontend entry point and its closed source pin remain unchanged.

Current tests use an explicitly modeled fixed-target transport around the production packet, bounds, owner, and budget code. A native parser oracle row supplies a Unicode byte-offset boundary; that data is not execution of the full guest header helper. The [validation record](../measurements/classic-header-discovery.json) reports 32 focused tests / 739 assertions, including all three graph test namespaces, and 984 complete optional runtime tests / 93,419 assertions before source-provider integration. The combined runner then passed 991 tests / 93,460 assertions; both records retain their actual input pins. Execution of the complete actual guest header helper through this new API remains a separate gate.
