# Standalone native startup evidence producer

The root compiled the standalone helper and passed its supervised native Init
and 24-case fixture gates; [validation.json](validation.json) pins the exact
sources, binary, outputs and receipts. Its author launched no native/JVM process.
No Java initialization, kernel admission or complete module-ready receipt is
produced here.

The new [NativeStartupEvidence source](../../../../lean/NativeStartupEvidence.lean)
is independent of the accepted NativeEntryEvidence and Export helpers. Its
bounded Name/type/IR serializers and complete static-closure walker are exact
marked copies from NativeEntryEvidence; `verify-source.py` checks those regions
and both unchanged accepted source pins. Duplication is intentional to keep
already accepted executable cohorts stable. No new helper is silently loaded
into an existing SourceBinding or live engine.

## Interface

`lean-native-startup-evidence --header SOURCE` parses exact UTF-8 source once
through original Parser.parseHeader, without line-ending normalization. It emits
`lean-project-header/2`: source byte extent, raw parser end, actual serialized
diagnostics and parserHasErrors. On error, header is null; consumers must refuse
it. A successful header contains actual module/prelude token presence, original
HeaderSyntax.imports with includeInit=false and true, explicit source spans, and
the actual inserted prefix. The latter includes ordinary AND meta Init when
the original interpreter inserts them. Nothing searches source text or uses a
grammar regex. Legacy explicit-meta and public+all invalid fixtures retain the
original parser error instead of manufacturing valid import flags.

`lean-native-startup-evidence --startup REQUEST.json` accepts:

```json
{
  "schema": "lean-native-startup-requests/1",
  "profile": "legacy-private-ordinary/1",
  "requestedImports": [
    {"module": ["str", ["anonymous"], "Init"],
     "importAll": false, "isExported": true, "isMeta": false}
  ]
}
```

The request chooses the ordinary roots to import. It is not source/type/phase
proof. This first profile accepts only nonanonymous string-component module
Names and those exact ordinary flag values; numeric/path-escape components,
meta/all requests and other profiles refuse. The source imports those original
tuples unchanged at private level with actual empty Options and loadExts=true.
It checks actual header mode/imports and captures effective ordered modules,
their phases/hasData/flags and actual inServer. An ordinary root import is not
the source header's automatically inserted meta Init tuple: preserve those two
different provenance layers when integrating project compilation.

Native import may execute native initializers/extension callbacks. This is an
explicit trusted native build boundary. The helper does not call another native
availability probe, infer per-module initialization status, or claim that the
future Java branch ran anything. The exported regular sequence is the original
interpreter fallback IF native module initialization is unavailable. The future
consumer must establish its own explicit no-native-symbol interpreter policy.

## Output and activation boundary

`lean-native-startup-evidence/1` retains, per actual module/index:

- Exact ordered regular module and IR entry arrays and builtin module/IR arrays.
- Regular fallback sequence: first list AS IS, then each IR pair absent from
  that original first list. This preserves duplicate first-list and IR-only
  pairs; it is not whole-list set deduplication.
- Actual module/decl IR phases, initRuntime and per-sequence selection decisions.
- For selected named pairs, actual target/action CI kinds, complete bounded
  closed types, safety flags, and native default-transparency Meta.isDefEq proof
  of actionType = IO(targetCI.type).
- Original raw global/action declarations and the actual original BASE-index
  boxed resolver result, with full declarations retained as closure roots.

The Java named transaction deliberately invokes the genuine RAW action with one
owned void World and object result. The native interpreter instead uses its
boxed resolver. Output distinguishes these routes; it does not call the raw
declaration the selected boxed declaration. Before Java activation the consumer
must structurally verify that the actual boxed bridge calls/forwards that raw
action and preserves its IO result. The producer supplies the original rows and
type relationship, not a fabricated bridge-equivalence Boolean.

Selected anonymous regular actions receive real IO Unit CI/type/callable
evidence but a v1 unsupported-activation reason. Nonempty builtin arrays are
preserved and unsupported; they are NOT appended to the regular fallback loop.
Repeated named target publication is also unsupported by the narrow Java
transaction while its original sequence remains preserved. Unsupported reasons
are source facts, not permission to skip an action. Consumers must recompute
their profile eligibility and refuse all unsupported obligations before effects.

IO.userError is a separately declared auxiliary codec root, never an initializer
or fake target. Its actual CI and native String → IO.Error equality proof, raw
ABI and full original body/closure are retained. The entropy consumer must also
verify that raw constructor body against its actual accepted row/layout; neither
this purpose label nor a displayed constructor name is layout authority.

The static union includes raw global/action, genuine boxed selection, redirect,
auxiliary and all dependency/error/panic rows. Overlapping canonical rows and
origins must agree. Initialized-global metadata and actual compiled-module
origin are retained; imported rows remain sourceLocal=false. Dynamic AP sites
are counted and dynamicClosureProven=false. Missing declarations/sorry dependencies
refuse. The saved Init census's original 60 raw action/global rows should be
covered; genuine boxed/codec roots may increase the final count. Do not force 60.

Runtime roles here are observations in the imported environment, not source
compilation receipts. Pinned ClosedTermCache and SimpleGroundExpr use ordinary
registerEnvExtension, whose state is not saved across imports. The actual Init
comparison found fifteen source-closed nullary declarations observed as generic
value after import, with identical full IR/ABI/occurrence dependencies and no
initializer. This is not inferred from `_closed_` text and neither record is
rewritten. The selected Java interpreter caches all nullary fdecls; only the
initialized role requires explicit publication. Consumers needing original
closed/ground source classification or native-C startup must obtain a tied
source-compilation receipt rather than reconstruct lost compiler caches.

The raw header mode intentionally disables mkInputContext's usual CRLF
normalization. Pinned whitespace rejects raw CR, including a CRLF pair at a
whitespace position. The CRLF fixture therefore expects the original parser
error and header=null while preserving all original bytes. A separate explicitly
derived LF-Unicode fixture tests successful raw byte spans. This strict mode
does not establish support for all files accepted by the normalizing frontend;
a future normalized mode needs its own provenance/position mapping.

## Bounds, compilation and receipts

Bounds: 64 KiB request, 1 MiB header source, 128 requested roots, 4,096 effective
modules, 16,384 raw attribute occurrences, 2,048 selected actions/IR closure rows,
32,768 pending IR names, 16,384 deps per row and 16 MiB final output. Type/Name
and IR depth/node/text budgets match the copied accepted serializer. Header
diagnostics are capped at64 actual messages/256 KiB rendered JSON. Hitting any
bound refuses, never truncates evidence.

Explicit root-supervised build only:

```sh
LEAN_SYSROOT=/configured/official/lean-4.33.1 \
  bash experiments/lean-ir/scripts/build-startup-evidence.sh emit
LEAN_SYSROOT=/configured/official/lean-4.33.1 \
  bash experiments/lean-ir/scripts/build-startup-evidence.sh selection-checks
LEAN_SYSROOT=/configured/official/lean-4.33.1 \
  bash experiments/lean-ir/scripts/build-startup-evidence.sh link
```

The [build script](../../../../scripts/build-startup-evidence.sh) checks the
reported compiler commit and available-memory floor, uses one Lean thread and
separate output paths. Typecheck/C emission, pure selection checks and native
link are separate commands so each can have its own recorded resource budget.
It is not itself
a complete process/RSS supervisor. Root must enforce one native process at a
time, 2 GiB MemAvailable floor, the approved RSS/CPU/wall/output limits and actual
owned-process cancellation. The author ran no native build; the root's actual
stage budgets/results are recorded separately in validation.json.

For EVERY accepted build/run preserve an external receipt with:

1. Source-manifest digest, every actual source/script/fixture digest, trusted
   toolchain descriptor, actual compiler/leanc hashes, complete command/options,
   generated C/olean/helper binary hashes and actual build exits/peak/time.
2. Independently expected helper binary/source cohort pins, actual request or
   header source bytes/hash, explicit LEAN_PATH/private module build products,
   exact imported fixture/Init olean cohort and target/commit/profile.
3. Actual stdout/stderr bytes/hash, process exit, wall/peak RSS, native-stop or
   interruption state, parser result or evidence output hash and semantic gates.
4. Explicit native-import-may-effect status and javaInitializationExecuted=false.

These receipts must come from the actual trusted native operation or independent
artifact pin. A caller-authored self-consistent manifest, copied expected count,
signature tag or ready Boolean is not evidence. This source-only manifest records
no fake binary/output hash or successful execution. No new source is activated
under a previously minted receipt.

## Root gates before acceptance

See [fixtures](../../../../test/fixtures/native-startup-evidence/README.md).
Compile named/anonymous/builtin/phase modules into a fresh private output tree.
Run the new helper with exact pinned binary and inputs under the root supervisor.
Verify original Init raw60 census coverage plus all extra bridge/codec rows,
one selected Random pair, empty builtin obligations for Init and complete static
closure/ABIs. Inspect actual boxed-to-raw bridge and IO.userError constructor.
Do not execute Random in Java as part of this producer gate.

Run header ordinary/prelude/module/meta/error and CRLF/Unicode cases, preserving
actual diagnostics/provenance. Compile the pure selection model to verify the
first-list/IR duplicate rule and all phase branches. Actual legacy/private
imports yield source all-phase decisions; that is not a runtime-phase skip test.
Those native gates passed on the recorded helper/source cohort. The
[serial gate script](../../../../scripts/gate-startup-evidence.py) accepts explicit
repository, toolchain/helper/exporter, old reference, census, existing Init output
and fresh output-directory paths. It runs under the root's process-group resource
supervisor, records every native command/output digest, continues independent
semantic failures and blocks startup dependent on a failed compile. It does not
invoke a Java runtime or mint a public artifact capability.

The root attempted emission on initial source `0e3054ac…`: the 900 MiB supervised
attempt stopped cleanly at sampled 921960 KiB without diagnostics; a separately
admitted 1.3 GiB attempt exited1 with three record-layout parse errors. Current
source separates JSON construction from uniformly indented record literals;
no type/lookup/selection policy changed. The source manifest preserves the two
negative receipt hashes. Neither attempt established accepted producer output.

The next attempt on source `c25900fb…` passed its resource gate but found two
type errors from one IO.userError proof binding: pinned mkArrow returns CoreM
Expr. That binding now uses monadic bind before native DefEq/instantiation. It
was the only mkArrow occurrence in this new producer. The corrected source
`f8c92d65…` then passed emission, selection checks and linking, producing helper
`2693f971…`. Ordinary Init produced 631 modules, one actual named Random pair
and 62 rows: the original raw60 plus the actual selected boxed action and the
separate IO.userError codec. It reported no unsupported activation reasons or
dynamic AP sites.

The first fixture batch recorded 21 passes and two failures. Investigation found
incorrect gate expectations, not IR/ABI changes: raw CRLF is rejected without
normalization, and source-only closed marks do not survive import. Original
outputs, bytes and hashes were preserved. The corrected batch passed all 24
cases: ten header cases, four compile/startup pairs, three invalid requests,
the compiler identity probe and two metadata/tool-pin checks. Its 62 common
declarations exactly matched old IR, ABI, dependency occurrences and redirects;
the fifteen closed→value observations and sourceLocal provenance difference are
reported explicitly. No role or original Header hash was spoofed.
