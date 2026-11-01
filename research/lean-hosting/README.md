# Maintained Lean frontend-hosting research

This tree maintains the source-frontend, checked-kernel association, import and fork research which is broader than the optional public Lean/JVM SDK. It is not a second production interpreter. The single canonical Java engine is in `modules/lean-jvm/src-java/ansatz/lean/jvm/internal/exec/Interpreter.java` at the repository root. Native SDK producer sources live under `tools/lean-producer`.

The public SDK and its release instructions are in [modules/lean-jvm](../../modules/lean-jvm/README.md). This tree does not claim that its hosted frontend, full Init import, kernel association, callbacks or fork profiles are public SDK features. Its admitted profiles and actual receipts remain separate.

## Layout and ownership

- `src/prototype/`: maintained legacy World backend, reusable typed readers, kernel bridges and comparison oracles. Prototype namespaces remain unchanged to preserve their contracts. This is research support, not a second SDK runtime.
- `test/prototype/`, `test/fixtures/`: active contract tests and source-native fixtures. Native oracles and captured bytes retain their independent provenance.
- `research/java-ir-baseline/`: existing Java-engine contract runner, explicit frontend controllers, source-module exchange, runtime-cohort and bootstrap work. The directory name is transitional; its immutable source layers and cwd-relative loaders are preserved rather than bulk rewritten. No Java interpreter source remains there.
- `research/`: other retained compiler/benchmark investigations and their documentation. Closed prepared-instruction, sparse-join and paged-register implementation clusters have been retired; their source is recoverable from the recorded Git commit.
- `lean/`, `native/`, `paired-init/`: hosted-frontend helpers, original-source oracles and bounded full-Init transport research. The four supported SDK helper sources have moved to `tools/lean-producer`; they are not duplicated here.
- `scripts/`: explicit research gates. They may require artifacts, core/kernel classes, a native toolchain or optional Pattern dependencies as their own profiles specify.
- `legacy-facade/`: unpublished provider-first `ansatz.lean` facade over the World backend. It is kept only for research compatibility and is not the `org.replikativ/ansatz-lean-jvm` release artifact.
- `measurements/`, `history/`: historical evidence and exact relocation/source-at-commit records. Historical runtime receipts are not current acceptance claims.

## Contract execution

Run research scripts from this directory, unless the script explicitly says otherwise. The repository-level `bin/run-test-contracts` compiles the canonical Java engine once into an isolated test JAR and runs its broad contract suite and maintained code-catalogue checks. `bin/run-lean-jvm-checks` independently checks the public SDK package and consumers. The unpublished legacy facade, World-wire, old cold-controller, coherent-consumer and Pattern experiments are an explicit optional lane: `bin/run-lean-hosting-research-checks`. Do not load experimental backends on the public SDK's classpath.

TaskRuntime's limited synchronous profile, code-demand/HostGuest boundaries, source/kernel bridges, graph import and eager fork remain maintained engine research. Their exclusion from the current public task-free SDK capability profile does not make them obsolete. Future cleanup must migrate their requirements and tests, not discard them by directory name.

## Historical material and retirement

[relocations-v1.json](history/relocations-v1.json) records the original path, destination and SHA-256 for each exact-byte move, plus the closed implementation cluster retired afterward. It identifies the original Git source commit. [The previous top-level research README](history/README-before-consolidation.md) is retained byte-for-byte as historical context; its old commands and relative links describe that earlier tree, not this maintained entry point.

Only closed benchmark implementations were removed. The World backend and numeric/block/Pattern compiler experiments remain research support with optional compatibility checks. World-wire serialization is retired as a public artifact target; it is not the SDK compiled-artifact format. Artifact serialization does not silently replace runtime World checkpoint or fork semantics. [The requirement mapping](CONTRACT_MIGRATION.md) identifies the canonical checks that keep structural, ownership, DAG, readiness and fork requirements mandatory.

No runtime/native acceptance is established by moving files. Source inventories and path checks can run without a JVM; the root operator owns fresh Java/SDK, frontend and native gates for the consolidated source cohort.
