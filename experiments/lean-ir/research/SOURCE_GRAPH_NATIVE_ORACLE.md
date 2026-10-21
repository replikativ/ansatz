# Source graph native prototype

This is G1 foundation work, not an issued runtime graph-import profile. The
existing `SourceModuleImport` helpers and runtime profiles remain unchanged.
`SourceModuleGraphImport.assembleClassicGraphOverInit` returns a pure `Except`
containing ordinary owned values. It does not check declarations, attest a
publication, run initializers, finalize imports, or issue a capability.

The caller must independently authenticate the exact native Init prefix, selected
source publication identities and worlds, local CI/unit correspondence, and empty
source initialization action lists. G0 resolves publication versions by identity;
this helper validates the resulting module/data inventory, not those capabilities.

The helper accepts classic source data with exactly implicit ordinary/meta Init
followed by ordinary source dependencies. Requested roots use the same header.
Parts must equal dependency-first DFS closure in actual root/dependency order.
Missing dependencies, cycles, extraneous parts, alternative topological orders,
module collisions, and cross-node constant/extra-name attribution collisions fail.
Native first-wins aliases and same-node constant-to-extra overlap remain valid.
Indices belong to each assembled attempt, never to a universal publication.

Inventory, edge, Name-spine/string-byte and region-key limits precede the scans
and map insertions they bound. Numeric Name segments are explicitly restricted to
UInt32.max and conservatively charge ten bytes each; there is no unbounded Name
rendering or numeric logarithm primitive. This is narrower than G0's bounded
canonical decimal wire representation. Future runtime projection must enforce
that restriction. Bounds do not replace authentication of the borrowed prefix.
All validation precedes `mkOwnedPart`; phase two preserves native records/parts
and appends source records with fixed private-classic effective flags.

The native oracle uses actual initializer-free Nat/String A → B → C sources and
then imports C to include all three modules. It directly finalizes owned logical
parts using the unchanged `finalizeClassic` (`leakEnv=false`). It never serializes
the logical chain, calls `freeRegions`, uses `withImportModules` cleanup, or passes
logical dependency regions to native save/read. The pinned Lean CLI independently compiles the same fixture texts to fresh
`.olean` files before the oracle starts; the disk reference imports C once.
Their hashes remain identical before and after the oracle. It compares
module order/effective flags and every resulting constant/extra attribution entry,
then checks Nat and Unicode function outputs. The synthetic diamond is structural
only; it is never finalized or evaluated. This is not hosted graph acceptance.

`check-source-graph-native.py` runs sequential native children under one 300-second
deadline, a 2048 MiB combined child-group/driver RSS ceiling and 2 GiB MemAvailable
floor, with at least 5 GiB available at launch. It pins all selected inputs before execution and retains every command's
stdout/stderr and failure receipt. It exports only tiny selected helper/fixture
closures, requires explicit empty action plans, rejects missing rows, and compares
external symbols plus borrowed parameter/result ABIs against exact original
producer CAS rows. A separately pinned capture from the live frozen consumer
provides actual supported primitive arities/signatures and six raw-handler ABIs.
Every external also needs that implemented support or an exact selected guest
redirect body/ABI; a declared deferred trap never counts as support. Legacy exporter
manifests contain version/target but no commit field: executable/source pins and
independent tool/oracle githash checks supply the explicitly limited provenance. It never exports all of Init. Actual G0 ordering/source
attribution comparison runs through Babashka without a JVM; native name inventory
is omitted from that G0 comparison, and native collision/attribution checks are
performed separately in the Lean helper/oracle.

Run from `experiments/lean-ir` with independently reviewed tool and input pins:

```sh
python3 scripts/check-source-graph-native.py --pins target/artifact-contract/source-graph-native-oracle/pins-reviewed.json --output target/artifact-contract/source-graph-native-oracle/run-fresh
```

The pin manifest supplies toolchain/exporter/Babashka locations and the admitted
producer store/index. Machine paths belong in ignored manifests, not tracked
configuration. Execution requires the campaign's resource-slot coordination.

The [portable validation record](../measurements/source-graph-native-oracle.json)
records the independently reviewed run-v8. All 15 native/Babashka commands passed
in 40.42 seconds, with 1,778,843,648-byte peak combined RSS and no guard stop.
The owned chain and independent CLI disk chain matched all 634 ordered effective
module records (631 native plus A/B/C), final requested imports, and all 95,098
constant/extra-name attribution entries. Both returned Nat 43 and String `Ωλλ`.
Eleven rejected inputs cover extra/unselected parts, alternate order, meta roots,
cross-source/native extra-name collisions, cycles, missing dependencies, excessive
depth, numeric overflow and oversized Name/key payloads. UInt32.max is accepted;
the diamond remains structural only. The unchanged G0 planner independently
matches the native module order and source attribution, with native collision and
attribution checks performed separately by the Lean oracle.

The new helper exports 173 local / 246 closure rows, with 36 reachable external
ABIs; all have exact producer CAS membership and actual captured primitive
support. Each fixture has two supported external ABIs. All four exported action
plans are explicitly empty. This support audit establishes external compatibility,
not hosted execution, complete IR lowerability, checked source publication,
finalizer callback authority, or a graph-import consumer capability. The unchanged
old import helper has its existing value initializer; its actions are not claimed
empty. No JVM or hosted graph execution was part of this gate.

Earlier trials remain preserved separately. Syntax-v1 exceeded its 768 MiB guard
while compiling the unchanged helper. Syntax-v2 reported reserved identifiers;
syntax-v3 typechecked their correction. Run-v2 rejected an unsupported borrowed
panic external before oracle execution; total checked collection operations
removed that dependency without adding bindings. Run-v3 then reported oracle
syntax errors before `main`. Run-v5 exceeded its 2 GiB RSS guard. Run-v6 exposed
the native initializer-execution flag being cleared after finalization; run-v8
re-enables it for the independent genuine disk import. None is relabeled as a
pass or resumed from a failed guest state. Proposed v4/v7 were never executed.

The immutable run-v8 manifest also pins the earlier research text. This updated
report does not change its captured evidence: a new reproduction must prepare and
independently review a fresh manifest for the current file bytes. The JSON
manifest contains `toolchain`, `exporter`, `bb`, `admittedStore`,
`admittedIndexSha256`, `runtimeCapabilities`, and `files` entries with exact paths,
byte counts and SHA-256 values. Its descriptive resource fields do not override
the driver's fixed guards. Machine paths stay in ignored local manifests. Keep
source/exporter provenance, the admitted producer catalogue, and the captured
actual runtime ABI inventory independently pinned; regenerating a manifest is
not authorization to trust new source or handlers.
