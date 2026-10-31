# Source4 policy bootstrap

This package replaces the historical selected-definition policy runners with explicit functions. Loading these namespaces performs no guest call, engine construction, source issuance or initializer execution. It requires the research loader's existing namespace order; it is not a standalone runtime boot.

`policies/requirements` returns the pinned fixture inventory. Copy each family into an exact file-set directory and pass those directories explicitly to `authenticate-policies!`, together with the actual catalogue and a pinned source reader `{:commit ... :read-blob! (fn [relative-path] byte-array)}`. The default index is package-relative; an external index must have the same independent SHA. Authentication checks all 77 upstream blobs and all 247 compact Header occurrences against complete original catalogue/CAS rows. The 28 fixture files contain complete raw ABI projections, historical state-coupling evidence and source hashes. Historical manifests may describe additional producer evidence files; those files are not silently treated as present in this selected package.

The stages are separate:

1. `setup-evidence!` authenticates the original thirteen setup rows and three required aliases. It returns the eight base helper labels and checked seams. It does not compose a receipt. Source4 adds its observer/exchange evidence and composes its four overlays once.
2. `policies-early/derive!` takes that actual receipt, a class basis, the complete authenticated extern fixture directory and its independent manifest SHA. It creates only an empty metadata Program to inspect actual registries. It authenticates all 961 original extern rows from the checked byte snapshot, excludes Native and all planned guest symbols, and deduplicates exact supported host ABIs. The returned descriptors provide no handler authority. Unsupported backend, lane and Native-ABI cases remain explicit coverage entries. The observer gate descriptor is separate; the heartbeat setter is installed once by the cohort.
3. `prepare-import-context` authenticates the heartbeat getter and disabled profiling getter, then delegates to the existing source context configuration. Source4 extends that result before capturing its single HostGuest policy.
4. `configure!` takes the actual imported driver, receipt, catalogue, bundle and optional caller-owned journal. The driver must already have authenticated demand attached, use the same class/Program/source, and be idle at instruction zero. Every policy Header comes through that demand's canonical memo. It installs the reviewed Meta, Level, Expr, pointer, compiler, String, Substring and finalizer bindings, audits all twenty-one actual Meta mappings, and returns the empty-native-symbol provider. It preserves the driver and current-context identity and records each completed stage. Failure preserves the actual journal and published metadata; it promises no rollback or guest-owner cleanup.

`description` retains the full historical state requirements as metadata. None of these stages admits a runtime capsule, proves initialized-global state or executes hidden helpers. The captured-runtime importer must independently establish the same-basis 534-global seed, lifecycle policies and source receipt. `close!` releases only the bundle's metadata registry entry.

Source-only verification:

```sh
python3 bootstrap/verify-policy-data.py --lean-repository /path/to/pinned-lean4
```

The repository argument is explicit and each blob is read with `git show` at the pinned commit, so a dirty checkout is not source authority. Root integration must definition-load both policy namespaces, exercise rejection models, derive the early descriptor census against the actual basis, configure one imported idle parent, and verify its actual guest mappings before any frontend command. No fresh boot or executable acceptance is claimed by this metadata audit.
